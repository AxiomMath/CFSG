module

public import Certificates.Data.S8DFin

public section

namespace Certificates.S8DFin

@[expose] def s8Rows (k : Nat) : Bool :=
  (List.range' (8 * k) 8).all fun x => (List.range 256).all fun y => okXY x y

theorem check_of_s8Rows (h : ∀ k < 32, s8Rows k = true) : check () = true := by
  simp only [check, List.all_eq_true, List.mem_range]
  intro x hx
  have hk := h (x / 8) (by omega)
  simp only [s8Rows, List.all_eq_true, List.mem_range'_1, List.mem_range] at hk
  exact hk x ⟨by omega, by omega⟩

set_option maxHeartbeats 0

theorem s8Rows_0 : s8Rows 0 = true := by decide +kernel
theorem s8Rows_1 : s8Rows 1 = true := by decide +kernel
theorem s8Rows_2 : s8Rows 2 = true := by decide +kernel
theorem s8Rows_3 : s8Rows 3 = true := by decide +kernel
theorem s8Rows_4 : s8Rows 4 = true := by decide +kernel
theorem s8Rows_5 : s8Rows 5 = true := by decide +kernel
theorem s8Rows_6 : s8Rows 6 = true := by decide +kernel
theorem s8Rows_7 : s8Rows 7 = true := by decide +kernel
theorem s8Rows_8 : s8Rows 8 = true := by decide +kernel
theorem s8Rows_9 : s8Rows 9 = true := by decide +kernel
theorem s8Rows_10 : s8Rows 10 = true := by decide +kernel
theorem s8Rows_11 : s8Rows 11 = true := by decide +kernel
theorem s8Rows_12 : s8Rows 12 = true := by decide +kernel
theorem s8Rows_13 : s8Rows 13 = true := by decide +kernel
theorem s8Rows_14 : s8Rows 14 = true := by decide +kernel
theorem s8Rows_15 : s8Rows 15 = true := by decide +kernel
theorem s8Rows_16 : s8Rows 16 = true := by decide +kernel
theorem s8Rows_17 : s8Rows 17 = true := by decide +kernel
theorem s8Rows_18 : s8Rows 18 = true := by decide +kernel
theorem s8Rows_19 : s8Rows 19 = true := by decide +kernel
theorem s8Rows_20 : s8Rows 20 = true := by decide +kernel
theorem s8Rows_21 : s8Rows 21 = true := by decide +kernel
theorem s8Rows_22 : s8Rows 22 = true := by decide +kernel
theorem s8Rows_23 : s8Rows 23 = true := by decide +kernel
theorem s8Rows_24 : s8Rows 24 = true := by decide +kernel
theorem s8Rows_25 : s8Rows 25 = true := by decide +kernel
theorem s8Rows_26 : s8Rows 26 = true := by decide +kernel
theorem s8Rows_27 : s8Rows 27 = true := by decide +kernel
theorem s8Rows_28 : s8Rows 28 = true := by decide +kernel
theorem s8Rows_29 : s8Rows 29 = true := by decide +kernel
theorem s8Rows_30 : s8Rows 30 = true := by decide +kernel
theorem s8Rows_31 : s8Rows 31 = true := by decide +kernel

end Certificates.S8DFin

namespace Certificates

open S8DFin in
theorem certificate442331 : S8DFin.check () = true :=
  check_of_s8Rows fun
    | 0, _ => s8Rows_0 | 1, _ => s8Rows_1 | 2, _ => s8Rows_2 | 3, _ => s8Rows_3
    | 4, _ => s8Rows_4 | 5, _ => s8Rows_5 | 6, _ => s8Rows_6 | 7, _ => s8Rows_7
    | 8, _ => s8Rows_8 | 9, _ => s8Rows_9 | 10, _ => s8Rows_10 | 11, _ => s8Rows_11
    | 12, _ => s8Rows_12 | 13, _ => s8Rows_13 | 14, _ => s8Rows_14 | 15, _ => s8Rows_15
    | 16, _ => s8Rows_16 | 17, _ => s8Rows_17 | 18, _ => s8Rows_18 | 19, _ => s8Rows_19
    | 20, _ => s8Rows_20 | 21, _ => s8Rows_21 | 22, _ => s8Rows_22 | 23, _ => s8Rows_23
    | 24, _ => s8Rows_24 | 25, _ => s8Rows_25 | 26, _ => s8Rows_26 | 27, _ => s8Rows_27
    | 28, _ => s8Rows_28 | 29, _ => s8Rows_29 | 30, _ => s8Rows_30 | 31, _ => s8Rows_31
    | _ + 32, h => absurd h (by omega)

end Certificates
