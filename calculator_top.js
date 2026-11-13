import {
    twos_complement,
    binary_string_to_int_list, int_list_to_binary_string,
    binary_point_alignment, list_to_string
} from './binary_support.js';

import {
    real_to_twos_comp_binary, hexadecimal_to_binary,
    ieee754_hex_to_binary, binary_to_real,
    binary_to_hexadecimal, binary_to_ieee754
} from './binary_conversions.js';

import {
    binary_division, binary_multiplier, binary_adder,
    binary_subtraction, binary_modulo, binary_twos_complement
} from './binary_math.js';

import { binary_and, binary_or, binary_xor, binary_not } from './binary_logic.js';
import {
	precision_profile, lookup_table
} from './binary_constants.js';

const HEX_NEGATIVE_LIST = ["8", "9", "A", "B", "C", "D", "E", "F", "a", "b", "c", "d", "e", "f"];

function isAlnum(ch) {
    return /^[a-z0-9]$/i.test(ch);
}

function compute_evaluation_step(main_display_value, input_mode, output_mode, int_bits, frac_bits, enable_print_statements = false) {
    const nibble_size = Math.floor(int_bits / 4);

    let {
        left: operand1,
        op: operator,
        right: operand2,
        operand1_present,
        operator_present,
        operand2_present,
        input_error
    } = parse_input_string(main_display_value);

    let operand1_data_error = false;
    let operand2_data_error = false;

    if (!input_error) {
        if (input_mode === "REAL") {
            operand1_data_error = verify_real_input(operand1);
            if (operand2 !== "") {
                operand2_data_error = verify_real_input(operand2);
            }
        } else if (input_mode === "HEX") {
            if (operand1.length > 0 && operand1.length < nibble_size) {
                const padChar = HEX_NEGATIVE_LIST.includes(operand1[0]) ? "F" : "0";
                operand1 = operand1.padStart(nibble_size, padChar);
            }
            operand1_data_error = verify_hex_input(operand1, int_bits, frac_bits);

            if (operand2_present) {
                if (operand2.length > 0 && operand2.length < nibble_size) {
                    const padChar = HEX_NEGATIVE_LIST.includes(operand2[0]) ? "F" : "0";
                    operand2 = operand2.padStart(nibble_size, padChar);
                }
                operand2_data_error = verify_hex_input(operand2, int_bits, frac_bits);
            }
        } else if (input_mode === "BIN") {
            operand1_data_error = verify_bin_input(operand1);
            if (operand2 !== "") {
                operand2_data_error = verify_bin_input(operand2);
            } else if (operator_present && !operand2_present) {
                operand2_data_error = true;
            }
        } else if (input_mode === "FP32") {
            operand1_data_error = verify_fp32_input(operand1);
            if (operand2_present) {
                operand2_data_error = verify_fp32_input(operand2);
            }
        } else if (input_mode === "FP64") {
            operand1_data_error = verify_fp64_input(operand1);
            if (operand2_present) {
                operand2_data_error = verify_fp64_input(operand2);
            }
        }
    }

    const operator_error = verify_operator(operator, input_mode, output_mode);

    if (!input_error) {
        if (((operand1.includes('.') || operand2.includes('.')) && ["&", "|", "^", "~"].includes(operator)) || (operator_error && operator !== "")) {
            if (["&", "|", "^", "~"].includes(operator)) {
                return ["", "Enter logic operands without radix point"];
            }
            return ["", "ERROR"];
        } else if (!operand1_data_error && !operand2_data_error && !operator_error) {
            let operand1_binary;
            if (["~", "!"].includes(operator) || (operand2_present && ["&", "|", "^"].includes(operator))) {
                operand1_binary = convert_to_binary(operand1, input_mode, int_bits, 0);
            } else {
                operand1_binary = convert_to_binary(operand1, input_mode, int_bits, frac_bits);
            }

            let calculator_result;
            if (operand2_present) {
                let operand2_binary;
                if (["&", "|", "^"].includes(operator)) {
                    operand2_binary = convert_to_binary(operand2, input_mode, int_bits, 0);
                } else {
                    operand2_binary = convert_to_binary(operand2, input_mode, int_bits, frac_bits);
                }
                const binary_result = binary_math_operation(operand1_binary, operand2_binary, operator, int_bits, frac_bits, output_mode, enable_print_statements);
                calculator_result = convert_from_binary(binary_result, output_mode);
            } else if (["~", "!", "2'S", "2's"].includes(operator)) {
                const binary_result = binary_math_operation(operand1_binary, null, operator, int_bits, frac_bits, output_mode, enable_print_statements);
                calculator_result = convert_from_binary(binary_result, output_mode);
            } else {
                calculator_result = convert_from_binary(operand1_binary, output_mode);
            }

            return [main_display_value, calculator_result];
        } else {
            return ["", "ERROR"];
        }
    } else {
        return ["", "ERROR"];
    }
}

function parse_input_string(input_string) {
    let state = 'Empty_String_Check';
    const data_length = input_string.length;
    let input_index = 0;
    let left = "", op = "", right = "";
    let operand1_present = false;
    let operator_present = false;
    let operand2_present = false;
    let input_error = false;

    while (true) {
        if (state === 'Empty_String_Check') {
            if (!input_string) {
                return { left: "", op: "", right: "", operand1_present: false, operator_present: false, operand2_present: false, input_error: true };
            }
            state = 'First_Character';
        } else if (state === 'First_Character') {
            if (input_string.startsWith("2's") || input_string.startsWith("2'S")) {
                op = "2'S";
                if (data_length > 3) {
                    input_index = 3;
                    state = 'First_Operand';
                    continue;
                } else {
                    return { left: "", op: "", right: "", operand1_present: false, operator_present: false, operand2_present: false, input_error: true };
                }
            }

            const ch = input_string[input_index];
            if (['+', '~', '!'].includes(ch)) {
                if (['~', '!'].includes(ch)) op = ch;
                if (data_length > 1) {
                    input_index += 1;
                    state = 'First_Operand';
                } else {
                    return { left: "", op: "", right: "", operand1_present: false, operator_present: false, operand2_present: false, input_error: true };
                }
            } else if (ch === '-' || isAlnum(ch) || ch === '.') {
                left += ch;
                if (data_length > 1) {
                    input_index += 1;
                    state = 'First_Operand';
                } else {
                    return { left, op, right, operand1_present, operator_present, operand2_present, input_error };
                }
            } else {
                return { left: "", op: "", right: "", operand1_present: false, operator_present: false, operand2_present: false, input_error: true };
            }
        } else if (state === 'First_Operand') {
            const ops = ["+", "-", "*", "/", "%", "&", "|", "^"];
            while (input_index < data_length && !ops.includes(input_string[input_index])) {
                const ch = input_string[input_index];
                if (isAlnum(ch) || ch === '.') {
                    left += ch;
                    if (input_index < data_length - 1) {
                        input_index += 1;
                    } else {
                        operand1_present = true;
                        return { left, op, right, operand1_present, operator_present, operand2_present, input_error };
                    }
                } else {
                    return { left: "", op: "", right: "", operand1_present: false, operator_present: false, operand2_present: false, input_error: true };
                }
            }

            operand1_present = true;
            operator_present = true;
            if (!['~', '!', "2'S"].includes(op)) {
                op = input_string[input_index];
            }
            input_index += 1;

            if (input_index < data_length) {
                state = 'Second_Operand';
            } else {
                operand2_present = false;
                return { left, op, right, operand1_present, operator_present, operand2_present, input_error };
            }
        } else if (state === 'Second_Operand') {
            while (input_index < data_length) {
                const ch = input_string[input_index];
                if (isAlnum(ch) || ch === '.' || (right === "" && ch === '-')) {
                    right += ch;
                    if (input_index < data_length - 1) {
                        input_index += 1;
                    } else {
                        operand2_present = true;
                        return { left, op, right, operand1_present, operator_present, operand2_present, input_error };
                    }
                } else {
                    return { left: "", op: "", right: "", operand1_present: false, operator_present: false, operand2_present: false, input_error: true };
                }
            }
            operand2_present = true;
            return { left, op, right, operand1_present, operator_present, operand2_present, input_error };
        }
    }
}
function verify_real_input(input_string) {
    return input_string.trim() === "" || isNaN(Number(input_string));
}

function verify_hex_input(input_string, int_bits, frac_bits) {
    if (!/^[0-9a-fA-F]+$/.test(input_string)) return true;
    return input_string.length > (int_bits + frac_bits) / 4;
}

function verify_bin_input(input_string) {
    const dotCount = (input_string.match(/\./g) || []).length;
    if (!/^[01.]+$/.test(input_string)) return true;
    return (dotCount > 1 || (input_string[0] !== '0' && input_string[0] !== '1') || input_string[input_string.length - 1] === '.');
}

function verify_fp32_input(input_string) {
    if (!/^[0-9a-fA-F]+$/.test(input_string)) return true;
    return input_string.length !== 8;
}

function verify_fp64_input(input_string) {
    if (!/^[0-9a-fA-F]+$/.test(input_string)) return true;
    return input_string.length !== 16;
}

function verify_operator(input_string, input_mode, output_mode) {
    let logic_error = false;
    if (["&", "|", "^", "~", "!", "2'S", "2's"].includes(input_string)) {
        logic_error = ["REAL", "FP32", "FP64"].includes(input_mode) || ["REAL", "FP32", "FP64"].includes(output_mode);
    }
    return (!["+", "-", "*", "/", "%", "&", "|", "^", "~", "!", "2'S", "2's", ""].includes(input_string)) || logic_error;
}

function convert_to_binary(operand, input_mode, int_bits, frac_bits) {
    if (input_mode === "REAL") {
        return binary_string_to_int_list(real_to_twos_comp_binary(operand, int_bits, frac_bits));
    } else if (input_mode === "HEX") {
        return binary_string_to_int_list(hexadecimal_to_binary(operand, int_bits, frac_bits, lookup_table));
    } else if (input_mode === "FP32") {
        return ieee754_hex_to_binary(operand, precision_profile["SINGLE"], lookup_table);
    } else if (input_mode === "FP64") {
        return ieee754_hex_to_binary(operand, precision_profile["DOUBLE"], lookup_table);
    } else {
        return binary_string_to_int_list(operand);
    }
}

function binary_math_operation(operand1, operand2, operator, int_bits, frac_bits, output_mode, enable_print_statements = false) {
    if (operator === "/") {
        let max_size = int_bits + frac_bits;
        if (output_mode === "FP32") max_size = Math.max(64, int_bits + frac_bits);
        else if (output_mode === "FP64") max_size = Math.max(128, int_bits + frac_bits);
        return binary_division(operand1, operand2, max_size);
    } else if (operator === "*") {
        return binary_multiplier(operand1, operand2);
    } else if (operator === "+") {
        const [addend_a, addend_b, op1_f, op2_f] = binary_point_alignment(operand1, operand2, false);
        const fraction_size = Math.max(op1_f, op2_f);
        const [n_sum, n_carry] = binary_adder(addend_a, addend_b);

        let sum_result;
        if ((operand1[0] === 0 && operand2[0] === 0 && n_sum[0] === 1) || (operand1[0] === 1 && operand2[0] === 1 && n_sum[0] === 0)) {
            sum_result = [n_carry, ...n_sum];
        } else {
            sum_result = n_sum;
        }

        const binary_point_index = sum_result.length - fraction_size;
        return [...sum_result.slice(0, binary_point_index), '.', ...sum_result.slice(binary_point_index)];
    } else if (operator === "-") {
        return binary_subtraction(operand1, operand2);
    } else if (operator === "%") {
        return binary_modulo(operand1, operand2, int_bits + frac_bits);
    } else if (operator === "&") {
        return binary_and(operand1, operand2);
    } else if (operator === "|") {
        return binary_or(operand1, operand2);
    } else if (operator === "^") {
        return binary_xor(operand1, operand2);
    } else if (operator === "~") {
        return binary_not(operand1);
    } else if (["!", "2'S", "2's"].includes(operator)) {
        return binary_twos_complement(operand1);
    }
}

function convert_from_binary(operand, output_mode) {
    if (output_mode === "REAL") {
        return binary_to_real(operand);
    } else if (output_mode === "HEX") {
        return binary_to_hexadecimal(operand, lookup_table);
    } else if (output_mode === "FP32") {
        return binary_to_ieee754(operand, precision_profile["SINGLE"], lookup_table);
    } else if (output_mode === "FP64") {
        return binary_to_ieee754(operand, precision_profile["DOUBLE"], lookup_table);
    } else {
        return int_list_to_binary_string(operand, operand.length).join("");
    }
}

// =====================================================================
// UI EVENT ROUTING
// =====================================================================
const inputBox = document.getElementById('input_box');
const outputBox = document.getElementById('output_box');
const intBitsBox = document.getElementById('int_bits_box');
const fracBitsBox = document.getElementById('frac_bits_box');
const useKeypadCheckbox = document.getElementById('use_keypad');
const keypadContainer = document.getElementById('keypad_container');
const pcButtonsContainer = document.getElementById('pc_buttons_container');
const helpModal = document.getElementById('help_modal');

function getSelectedRadio(name) {
    const checked = document.querySelector(`input[name="${name}"]:checked`);
    return checked ? checked.value : "REAL";
}

let currentOutputValue = "";
let currentOutputType = "";

function processButton(val) {
    if (val === "R" || val === "Reset") {
        inputBox.value = "";
        outputBox.textContent = "";
        return;
    }

    if (val === "Enter" || val === "=") {
        const inputMode = getSelectedRadio("input_mode");
        const outputMode = getSelectedRadio("output_mode");
        const intBits = parseInt(intBitsBox.value, 10) || 16;
        const fracBits = parseInt(fracBitsBox.value, 10) || 16;

        const [mainVal, calcResult] = compute_evaluation_step(
            inputBox.value,
            inputMode,
            outputMode,
            intBits,
            fracBits,
            false
        );
        inputBox.value = mainVal;
        outputBox.textContent = calcResult;
		currentOutputValue = calcResult;
		currentOutputType = outputMode;
    }
    else if (val === "Back")
    {
        inputBox.value = inputBox.value.slice(0, -1);
    }
	else if (val === 'Type') {
		if (currentOutputValue !== "" && currentOutputValue !== "ERROR") {
			const outputMode = getSelectedRadio("output_mode");
			const intBits = parseInt(intBitsBox.value, 10) || 16;
			const fracBits = parseInt(fracBitsBox.value, 10) || 16;
       		console.log('Input = ', currentOutputValue, 'Input type = ', currentOutputType, 'Output type = ', outputMode);

			const [updated_main, updated_aux] = compute_evaluation_step(
				currentOutputValue,
				currentOutputType,
				outputMode,
				intBits,
				fracBits,
				false
			);

			// Render back to UI
//			inputBox.value = mainVal;
			outputBox.textContent = updated_aux;
		}
	}
    else
    {
        inputBox.value += val;
    }
}

document.querySelectorAll('[data-key]').forEach(btn => {
    btn.addEventListener('click', () => {
        processButton(btn.getAttribute('data-key'));
    });
});

inputBox.addEventListener('keydown', (e) => {
    if (e.key === 'Enter') {
        e.preventDefault();
        processButton('Enter');
    }
});

useKeypadCheckbox.addEventListener('change', () => {
    if (useKeypadCheckbox.checked) {
        keypadContainer.style.display = 'grid';
        pcButtonsContainer.style.display = 'none';
        inputBox.setAttribute('readonly', true);
    } else {
        keypadContainer.style.display = 'none';
        pcButtonsContainer.style.display = 'flex';
        inputBox.removeAttribute('readonly');
    }
});

// Trigger off of a change to the output format
document.getElementById('output_mode_container').addEventListener('change', function() {
	processButton('Type');
});

document.getElementById('btn_help').addEventListener('click', () => {
    helpModal.style.display = 'flex';
});

document.getElementById('btn_close_help').addEventListener('click', () => {
    helpModal.style.display = 'none';
});

helpModal.addEventListener('click', (e) => {
    if (e.target === helpModal) {
        helpModal.style.display = 'none';
    }
});
