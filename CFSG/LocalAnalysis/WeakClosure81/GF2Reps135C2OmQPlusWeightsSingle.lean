module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusWeights

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin

variable {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ}
  (hm : m = Nat.card Fˣ) {k : Type} [Field k] (ι : F →+* k)

include hn hm in
theorem omq_omPlus_wt_single (b : Fin n) (c : ℕ) {g : spinGroup (quadPlus n F)}
    (hg : g ∈ (omPlusCurtisDatum n F hn).H) :
    omqPlusWt ι (Pi.single b (c : ZMod m)) g = ι (omqPlusEntry n g b) ^ c := by
  have hne : omqPlusEntry n g b ≠ 0 := ((omq_omPlus_H_diagonal (hn := hn) hg).2 b).1
  have hpow : ι (omqPlusEntry n g b) ^ m = 1 := by
    have h1 : (Units.mk0 (omqPlusEntry n g b) hne) ^ m = 1 := by
      rw [hm]
      exact pow_card_eq_one'
    have h2 : ((Units.mk0 (omqPlusEntry n g b) hne : Fˣ) : F) ^ m = 1 := by
      simpa using congrArg (fun u : Fˣ => (u : F)) h1
    have h3 : (ι (((Units.mk0 (omqPlusEntry n g b) hne : Fˣ) : F))) ^ m = 1 := by
      rw [← map_pow, h2, map_one]
    rwa [Units.val_mk0] at h3
  simp only [omqPlusWt]
  rw [Finset.prod_eq_single_of_mem (s := Finset.univ) b (Finset.mem_univ b)]
  · rw [Pi.single_eq_same, ZMod.val_natCast]
    conv_rhs => rw [← Nat.mod_add_div c m]
    rw [pow_add, pow_mul, hpow, one_pow, mul_one]
  · intro b' _ hb'
    rw [Pi.single_eq_of_ne hb', ZMod.val_zero, pow_zero]

end CFSG.LocalAnalysis.WeakClosure81
