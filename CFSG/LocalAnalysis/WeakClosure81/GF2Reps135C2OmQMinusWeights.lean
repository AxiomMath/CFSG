module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusTorus

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

private theorem c2slomqmw3_toral_pow_eq_one {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k : Type*} [Field k] (ι : K →+* k)
    (ι' : ShortField b c →+* k) {g : spinGroup (quadMinus n K b c)} {t : Fin (n - 1) → Kˣ}
    {z : ShortField b c} (hg : OmqMinusToral n g t z) :
    (∀ i, ι (t i : K) ^ Nat.card Kˣ = 1) ∧ ι' z ^ (Nat.card K + 1) = 1 := by
  refine ⟨fun i => ?_, ?_⟩
  · rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one', Units.val_one, map_one]
  · rw [← map_pow, omq_shortField_pow_card_succ hirr, hg.2.2.1, map_one, map_one]

theorem omq_omMinus_wt_mul {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k : Type*} [Field k] {m h : ℕ}
    (ι : K →+* k) (ι' : ShortField b c →+* k) (ν : OmqMinusLat (n - 1) m h)
    {g g' : spinGroup (quadMinus n K b c)} (hg : g ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H)
    (hg' : g' ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H) :
    omqMinusWt n ι ι' ν (g * g') = omqMinusWt n ι ι' ν g * omqMinusWt n ι ι' ν g' := by
  obtain ⟨t, z, ht⟩ := omq_omMinus_H_toral hn hirr hg
  obtain ⟨t', z', ht'⟩ := omq_omMinus_H_toral hn hirr hg'
  rw [omq_omMinus_wt_eq_of_toral ι ι' ν (ht.mul ht'), omq_omMinus_wt_eq_of_toral ι ι' ν ht,
    omq_omMinus_wt_eq_of_toral ι ι' ν ht']
  simp only [Pi.mul_apply, Units.val_mul, map_mul, mul_pow, Finset.prod_mul_distrib]
  ring

theorem omq_omMinus_wt_add {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k : Type*} [Field k] {m h : ℕ}
    (hm : m = Nat.card Kˣ) (hh : h = Nat.card K + 1) (ι : K →+* k) (ι' : ShortField b c →+* k)
    (ν ν' : OmqMinusLat (n - 1) m h) {g : spinGroup (quadMinus n K b c)}
    (hg : g ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H) :
    omqMinusWt n ι ι' (ν + ν') g = omqMinusWt n ι ι' ν g * omqMinusWt n ι ι' ν' g := by
  haveI : NeZero m := ⟨by rw [hm]; exact Nat.card_pos.ne'⟩
  haveI : NeZero h := ⟨by omega⟩
  obtain ⟨t, z, ht⟩ := omq_omMinus_H_toral hn hirr hg
  obtain ⟨hpt, hpz⟩ := c2slomqmw3_toral_pow_eq_one hirr ι ι' ht
  rw [omq_omMinus_wt_eq_of_toral ι ι' (ν + ν') ht, omq_omMinus_wt_eq_of_toral ι ι' ν ht,
    omq_omMinus_wt_eq_of_toral ι ι' ν' ht]
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
  have e1 : ∀ i, ι (t i : K) ^ ((ν.1 i + ν'.1 i).val) =
      ι (t i : K) ^ (ν.1 i).val * ι (t i : K) ^ (ν'.1 i).val := by
    intro i
    rw [← pow_add]
    conv_rhs => rw [pow_eq_pow_mod (a := ι (t i : K)) (n := m) _ (by rw [hm]; exact hpt i)]
    rw [ZMod.val_add]
  have e2 : ι' z ^ ((ν.2 + ν'.2).val) = ι' z ^ ν.2.val * ι' z ^ ν'.2.val := by
    rw [← pow_add]
    conv_rhs => rw [pow_eq_pow_mod (a := ι' z) (n := h) _ (by rw [hh]; exact hpz)]
    rw [ZMod.val_add]
  rw [Finset.prod_congr rfl (fun i _ => e1 i), Finset.prod_mul_distrib, e2]
  ring

theorem omq_omMinus_wt_neg {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k : Type*} [Field k] {m h : ℕ}
    (hm : m = Nat.card Kˣ) (hh : h = Nat.card K + 1) (ι : K →+* k) (ι' : ShortField b c →+* k)
    (ν : OmqMinusLat (n - 1) m h) {g : spinGroup (quadMinus n K b c)}
    (hg : g ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H) :
    omqMinusWt n ι ι' (-ν) g = (omqMinusWt n ι ι' ν g)⁻¹ := by
  have e := omq_omMinus_wt_add hn hirr hm hh ι ι' ν (-ν) hg
  rw [add_neg_cancel] at e
  have e0 : omqMinusWt n ι ι' (0 : OmqMinusLat (n - 1) m h) g = 1 := by
    simp [omqMinusWt]
  rw [e0] at e
  exact eq_inv_of_mul_eq_one_right e.symm

theorem omq_omMinus_wt_nsmul {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k : Type*} [Field k] {m h : ℕ}
    (hm : m = Nat.card Kˣ) (hh : h = Nat.card K + 1) (ι : K →+* k) (ι' : ShortField b c →+* k)
    (j : ℕ) (ν : OmqMinusLat (n - 1) m h) {g : spinGroup (quadMinus n K b c)}
    (hg : g ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H) :
    omqMinusWt n ι ι' (j • ν) g = omqMinusWt n ι ι' ν g ^ j := by
  induction j with
  | zero =>
    rw [zero_nsmul, pow_zero]
    simp [omqMinusWt]
  | succ j ih =>
    rw [succ_nsmul, omq_omMinus_wt_add hn hirr hm hh ι ι' (j • ν) ν hg, ih, pow_succ]

theorem omq_omMinus_wt_zero {n : ℕ} {K : Type*} [Field K] {b c : K} {k : Type*} [Field k]
    {m h : ℕ} (ι : K →+* k) (ι' : ShortField b c →+* k) (g : spinGroup (quadMinus n K b c)) :
    omqMinusWt n ι ι' (0 : OmqMinusLat (n - 1) m h) g = 1 := by
  simp [omqMinusWt]

theorem omq_omMinus_wt_single {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k : Type*} [Field k] {m h : ℕ}
    (hm : m = Nat.card Kˣ) (ι : K →+* k) (ι' : ShortField b c →+* k) (i : Fin (n - 1)) (cc : ℕ)
    {g : spinGroup (quadMinus n K b c)} (hg : g ∈ (SmallO8mCurtis.curtisDatum n hn hirr).H) :
    omqMinusWt n ι ι' ((Pi.single i (cc : ZMod m), (0 : ZMod h)) : OmqMinusLat (n - 1) m h) g =
      ι (mat n g (.inl i) (.inl i)) ^ cc := by
  haveI : NeZero m := ⟨by rw [hm]; exact Nat.card_pos.ne'⟩
  obtain ⟨t, z, ht⟩ := omq_omMinus_H_toral hn hirr hg
  obtain ⟨hpt, hpz⟩ := c2slomqmw3_toral_pow_eq_one hirr ι ι' ht
  rw [omq_omMinus_wt_eq_of_toral ι ι' _ ht, ht.mat_inl_inl]
  simp only [ZMod.val_zero, pow_zero, mul_one]
  rw [Finset.prod_eq_single_of_mem i (Finset.mem_univ i)]
  · rw [Pi.single_eq_same, ZMod.val_natCast]
    conv_rhs => rw [← Nat.mod_add_div cc m]
    rw [pow_add, pow_mul, show ι (t i : K) ^ m = 1 by rw [hm]; exact hpt i, one_pow, mul_one]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, ZMod.val_zero, pow_zero]

end CFSG.LocalAnalysis.WeakClosure81
