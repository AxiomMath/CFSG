module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusWeights

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin

variable {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ}
  (hm : m = Nat.card Fˣ) {k : Type} [Field k] (ι : F →+* k)

include hn hm in
private lemma c2slomqwa_entry_pow_eq_one {g : spinGroup (quadPlus n F)}
    (hg : g ∈ (omPlusCurtisDatum n F hn).H) (b : Fin n) :
    ι (omqPlusEntry n g b) ^ m = 1 := by
  have hne : omqPlusEntry n g b ≠ 0 := ((omq_omPlus_H_diagonal hn hg).2 b).1
  let t : Fˣ := Units.mk0 (omqPlusEntry n g b) hne
  have ht : (t : F) = omqPlusEntry n g b := Units.val_mk0 hne
  have hu : (ι (t : F)) ^ Nat.card Fˣ = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one', Units.val_one, map_one]
  rw [hm, ← ht]
  exact hu

include hn hm in
theorem omq_omPlus_wt_add (ν ν' : Fin n → ZMod m) {g : spinGroup (quadPlus n F)}
    (hg : g ∈ (omPlusCurtisDatum n F hn).H) :
    omqPlusWt ι (ν + ν') g = omqPlusWt ι ν g * omqPlusWt ι ν' g := by
  haveI : NeZero m := ⟨by rw [hm]; exact Nat.card_pos.ne'⟩
  simp only [omqPlusWt, Pi.add_apply]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [← pow_add]
  conv_rhs =>
    rw [pow_eq_pow_mod (a := ι (omqPlusEntry n g b)) (n := m) _
      (c2slomqwa_entry_pow_eq_one hn hm ι hg b)]
  rw [ZMod.val_add]

include hn hm in
theorem omq_omPlus_wt_neg (ν : Fin n → ZMod m) {g : spinGroup (quadPlus n F)}
    (hg : g ∈ (omPlusCurtisDatum n F hn).H) :
    omqPlusWt ι (-ν) g = (omqPlusWt ι ν g)⁻¹ := by
  have h := omq_omPlus_wt_add hn hm ι ν (-ν) hg
  rw [add_neg_cancel] at h
  have h0 : omqPlusWt ι (0 : Fin n → ZMod m) g = 1 := by simp [omqPlusWt]
  rw [h0] at h
  exact eq_inv_of_mul_eq_one_right h.symm

include hn hm in
theorem omq_omPlus_wt_nsmul (j : ℕ) (ν : Fin n → ZMod m) {g : spinGroup (quadPlus n F)}
    (hg : g ∈ (omPlusCurtisDatum n F hn).H) :
    omqPlusWt ι (j • ν) g = omqPlusWt ι ν g ^ j := by
  induction j with
  | zero =>
    rw [zero_nsmul, pow_zero]
    simp [omqPlusWt]
  | succ j ih =>
    rw [succ_nsmul, omq_omPlus_wt_add hn hm ι (j • ν) ν hg, ih, pow_succ]

end CFSG.LocalAnalysis.WeakClosure81
