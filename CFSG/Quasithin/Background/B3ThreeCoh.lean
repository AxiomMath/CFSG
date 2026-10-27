module

public import CFSG.Quasithin.Background.B3ThreeGen

public section

namespace CFSG.Quasithin.B3

set_option maxRecDepth 100000

theorem chkH1_five_ut0 : chkH1 5 Mod.ut0 false = true := by decide +kernel
theorem chkH1_seven_ut0 : chkH1 7 Mod.ut0 false = true := by decide +kernel
theorem chkH1_six_ut0 : chkH1 6 Mod.ut0 true = true := by decide +kernel
theorem chkH1_six_u0 : chkH1 6 Mod.u0 true = true := by decide +kernel
theorem chkNP_six_ut0 : chkNP 6 Mod.ut0 = true := by decide +kernel
theorem chkNP_eight_ut0 : chkNP 8 Mod.ut0 = true := by decide +kernel
theorem chkNP_six_u0 : chkNP 6 Mod.u0 = true := by decide +kernel
theorem chkNP_eight_u0 : chkNP 8 Mod.u0 = true := by decide +kernel

theorem cands_eight_ut0 : cands 8 Mod.ut0 = [0, 3, 5, 6, 249, 250, 252, 255] := by decide +kernel
theorem cands_eight_u0 : cands 8 Mod.u0 = [0, 3, 5, 6] := by decide +kernel

theorem row_eight_ut0_0 : chkRow 8 Mod.ut0 true 0 = true := by decide +kernel
theorem row_eight_ut0_3 : chkRow 8 Mod.ut0 true 3 = true := by decide +kernel
theorem row_eight_ut0_5 : chkRow 8 Mod.ut0 true 5 = true := by decide +kernel
theorem row_eight_ut0_6 : chkRow 8 Mod.ut0 true 6 = true := by decide +kernel
theorem row_eight_ut0_249 : chkRow 8 Mod.ut0 true 249 = true := by decide +kernel
theorem row_eight_ut0_250 : chkRow 8 Mod.ut0 true 250 = true := by decide +kernel
theorem row_eight_ut0_252 : chkRow 8 Mod.ut0 true 252 = true := by decide +kernel
theorem row_eight_ut0_255 : chkRow 8 Mod.ut0 true 255 = true := by decide +kernel

theorem row_eight_u0_0 : chkRow 8 Mod.u0 true 0 = true := by decide +kernel
theorem row_eight_u0_3 : chkRow 8 Mod.u0 true 3 = true := by decide +kernel
theorem row_eight_u0_5 : chkRow 8 Mod.u0 true 5 = true := by decide +kernel
theorem row_eight_u0_6 : chkRow 8 Mod.u0 true 6 = true := by decide +kernel

theorem chkH1_eight_ut0 : chkH1 8 Mod.ut0 true = true := by
  unfold chkH1
  rw [cands_eight_ut0]
  simp only [List.all_cons, List.all_nil, Bool.and_true, row_eight_ut0_0, row_eight_ut0_3,
    row_eight_ut0_5, row_eight_ut0_6, row_eight_ut0_249, row_eight_ut0_250, row_eight_ut0_252,
    row_eight_ut0_255]

theorem chkH1_eight_u0 : chkH1 8 Mod.u0 true = true := by
  unfold chkH1
  rw [cands_eight_u0]
  simp only [List.all_cons, List.all_nil, Bool.and_true, row_eight_u0_0, row_eight_u0_3,
    row_eight_u0_5, row_eight_u0_6]

theorem H1_natural_odd {n : ℕ} (hn : n = 5 ∨ n = 7) : ZeroClass (actL n Mod.ut0) := by
  rcases hn with rfl | rfl
  · exact zeroClass_of_chk (Or.inl rfl) _ chkH1_five_ut0
  · exact zeroClass_of_chk (Or.inr (Or.inr (Or.inl rfl))) _ chkH1_seven_ut0

theorem H1_natural_even {n : ℕ} (hn : n = 6 ∨ n = 8) :
    TwoClass (actL n Mod.ut0) (d0 n Mod.ut0) := by
  rcases hn with rfl | rfl
  · exact twoClass_of_chk (Or.inr (Or.inl rfl)) (Or.inr rfl) chkH1_six_ut0 chkNP_six_ut0
  · exact twoClass_of_chk (Or.inr (Or.inr (Or.inr rfl))) (Or.inr rfl) chkH1_eight_ut0
      chkNP_eight_ut0

theorem H1_core_even {n : ℕ} (hn : n = 6 ∨ n = 8) :
    TwoClass (actL n Mod.u0) (d0 n Mod.u0) := by
  rcases hn with rfl | rfl
  · exact twoClass_of_chk (Or.inr (Or.inl rfl)) (Or.inl rfl) chkH1_six_u0 chkNP_six_u0
  · exact twoClass_of_chk (Or.inr (Or.inr (Or.inr rfl))) (Or.inl rfl) chkH1_eight_u0
      chkNP_eight_u0

theorem card_H1_natural_odd {n : ℕ} (hn : n = 5 ∨ n = 7) :
    Nat.card (H1 (actL n Mod.ut0)) = 1 :=
  (H1_natural_odd hn).card_H1

theorem card_H1_natural_even {n : ℕ} (hn : n = 6 ∨ n = 8) :
    Nat.card (H1 (actL n Mod.ut0)) = 2 :=
  (H1_natural_even hn).card_H1 (V_sq' _)

end CFSG.Quasithin.B3
