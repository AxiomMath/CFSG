module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusTorus

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

@[expose] noncomputable def omqMinusEntryHom {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (i : Fin (n - 1)) :
    (SmallO8mCurtis.curtisDatum n hn hirr).H →* Kˣ where
  toFun g := Units.mk0 (mat n g.1 (.inl i) (.inl i)) (by
    obtain ⟨t, z, ht⟩ := omq_omMinus_H_toral hn hirr g.2
    rw [ht.mat_inl_inl]
    exact (t i).ne_zero)
  map_one' := by
    apply Units.ext
    simp [mat_one]
  map_mul' g g' := by
    apply Units.ext
    obtain ⟨t, z, ht⟩ := omq_omMinus_H_toral hn hirr g.2
    obtain ⟨t', z', ht'⟩ := omq_omMinus_H_toral hn hirr g'.2
    have hm := ht.mul ht'
    simp only [Units.val_mk0, Units.val_mul]
    show mat n (g.1 * g'.1) (.inl i) (.inl i) = _
    rw [hm.mat_inl_inl, ht.mat_inl_inl, ht'.mat_inl_inl]
    simp

theorem omqMinusEntryHom_val {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (i : Fin (n - 1))
    (g : (SmallO8mCurtis.curtisDatum n hn hirr).H) :
    ((omqMinusEntryHom hn hirr i g : Kˣ) : K) = mat n g.1 (.inl i) (.inl i) := rfl

@[expose] noncomputable def omqMinusZHom {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (SmallO8mCurtis.curtisDatum n hn hirr).H →* (ShortField b c)ˣ := by
  haveI := fact_shortField hirr
  exact
  { toFun := fun g => Units.mk0 (omqMinusZ n g.1) (by
      obtain ⟨t, z, ht⟩ := omq_omMinus_H_toral hn hirr g.2
      rw [ht.omqMinusZ_eq]
      intro h0
      have h1 := ht.2.2.1
      rw [h0, QuadraticAlgebra.norm_zero] at h1
      exact zero_ne_one h1)
    map_one' := by
      apply Units.ext
      simp only [Units.val_mk0, Units.val_one]
      exact (OmqMinusToral.one n (b := b) (c := c)).omqMinusZ_eq
    map_mul' := fun g g' => by
      apply Units.ext
      obtain ⟨t, z, ht⟩ := omq_omMinus_H_toral hn hirr g.2
      obtain ⟨t', z', ht'⟩ := omq_omMinus_H_toral hn hirr g'.2
      simp only [Units.val_mk0, Units.val_mul]
      show omqMinusZ n (g.1 * g'.1) = _
      rw [(ht.mul ht').omqMinusZ_eq, ht.omqMinusZ_eq, ht'.omqMinusZ_eq] }

theorem omqMinusZHom_val {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (g : (SmallO8mCurtis.curtisDatum n hn hirr).H) :
    ((omqMinusZHom hn hirr g : (ShortField b c)ˣ) : ShortField b c) = omqMinusZ n g.1 := rfl

end CFSG.LocalAnalysis.WeakClosure81
