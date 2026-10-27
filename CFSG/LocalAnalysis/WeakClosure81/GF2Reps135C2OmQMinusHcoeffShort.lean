module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQHcoeffGen
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusGauss
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusShortWeyl
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusTorus

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.Quasithin.SmithCurtis
open CFSG.LieType.RootSystem CFSG.LieType.Steinberg
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

theorem omq_omMinus_shortPosHom_mem_U {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (i : Fin (n - 1))
    (p : Fin 2 → K) :
    shortPosHom n hirr i (Multiplicative.ofAdd p) ∈ (SmallO8mCurtis.curtisDatum n hn hirr).U := by
  have hγ : toStdB (n - 1) (ofStdB (n - 1) (Pi.single i 1)) = Pi.single i (boolSign true) := by
    rw [boolSign_true]
    exact toStdB_ofStdB _ _
  have hroot : ofStdB (n - 1) (Pi.single i 1) ∈ roots (isFiniteType_cartanB (n - 1)) ∅ :=
    mem_roots_of_toStdB_eq_short n i true hγ
  have hht : 0 < ht (ofStdB (n - 1) (Pi.single i 1) : Fin (n - 1) → ℤ) :=
    (ht_pos_iff_of_toStdB_eq_single (n - 1) (Or.inl rfl)
      (by rw [boolSign_true] at hγ; exact hγ)).2 rfl
  have hmem : shortPosHom n hirr i (Multiplicative.ofAdd p) ∈
      minusRootGroup n hirr (ofStdB (n - 1) (Pi.single i 1)) := by
    rw [minusRootGroup_eq_short n hirr i true hγ]
    exact ⟨Multiplicative.ofAdd p, rfl⟩
  exact rootGroup_le_posUnipotent (D := minusDatum n hirr) hroot hht hmem

theorem omq_omMinus_shortNegHom_mem_L {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (i : Fin (n - 1))
    (p : Fin 2 → K) :
    shortNegHom n hirr i (Multiplicative.ofAdd p) ∈ (SmallO8mCurtis.curtisDatum n hn hirr).L := by
  have hγ : toStdB (n - 1) (ofStdB (n - 1) (Pi.single i (-1))) = Pi.single i (boolSign false) := by
    rw [boolSign_false]
    exact toStdB_ofStdB _ _
  have hroot : ofStdB (n - 1) (Pi.single i (-1)) ∈ roots (isFiniteType_cartanB (n - 1)) ∅ :=
    mem_roots_of_toStdB_eq_short n i false hγ
  have hht : ht (ofStdB (n - 1) (Pi.single i (-1)) : Fin (n - 1) → ℤ) < 0 := by
    rw [boolSign_false] at hγ
    rw [ht_of_toStdB_eq_single (n - 1) hγ]
    have := i.isLt
    omega
  have hmem : shortNegHom n hirr i (Multiplicative.ofAdd p) ∈
      minusRootGroup n hirr (ofStdB (n - 1) (Pi.single i (-1))) := by
    rw [minusRootGroup_eq_short n hirr i false hγ]
    exact ⟨Multiplicative.ofAdd p, rfl⟩
  exact rootGroup_le_negUnipotent (D := minusDatum n hirr) hroot hht hmem

theorem omq_omMinus_hcoeff_short {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k : Type} [Field k]
    [CharP k 2] (ι' : ShortField b c →+* k) {V : Type} [AddCommGroup V] [Module k V]
    {σ : Representation k (spinGroup (quadMinus n K b c)) V} (hσ : IsSimpleRep σ) {y : V}
    {χ : spinGroup (quadMinus n K b c) → k} {μ : Fin (n - 1) → k}
    (ht : (SmallO8mCurtis.curtisDatum n hn hirr).IsCurtisType σ y χ μ)
    (hex : ∃ j : Fin (n - 1), μ j = (SmallO8mCurtis.curtisDatum n hn hirr).dScalar χ j)
    {C : ℕ} (hC : 1 ≤ C)
    (hχ : ∀ u : (ShortField b c)ˣ,
      χ (shortTorusHom n hirr ⟨0, by omega⟩ u) = ι' (u : ShortField b c) ^ C) :
    ∃ φ : Module.Dual k V, φ y = 1 ∧ ∀ s t : ShortField b c,
      φ (σ (shortX n hirr ⟨0, by omega⟩ s * shortY n hirr ⟨0, by omega⟩ t) y) =
        (1 + ι' s * ι' t) ^ C := by
  classical
  haveI := fact_shortField hirr
  haveI := finite_shortField (b := b) (c := c)
  let D := SmallO8mCurtis.curtisDatum n hn hirr
  let i0 : Fin (n - 1) := ⟨0, by omega⟩
  let R := shortRels n hirr i0
  have hh : ∀ a : (ShortField b c)ˣ, R.h (a : ShortField b c) = shortTorusHom n hirr i0 a := by
    intro a
    rw [shortRels_h, shortTorusHom_apply]
  have hN : σ (R.w 1) y ∈ augSub σ D.L := by
    rw [shortRels_w_one]
    exact omq_omMinus_shortWeyl_mem_augSub hn hirr ht hex
  refine omq_curtis_hcoeff_of_bruhat D ι' hσ ht (fun a => R.x a) (fun a => R.y a)
    (fun a : (ShortField b c)ˣ => shortTorusHom n hirr i0 a) (R.w 1)
    (fun a => omq_omMinus_shortPosHom_mem_U hn hirr i0 _)
    (fun a => omq_omMinus_shortNegHom_mem_L hn hirr i0 _)
    (fun u => (omq_omMinus_torus_mem_H hn hirr).2 i0 u) hC hχ ?_ ?_ hN
  · intro s t hd
    have h := omq_rankOneRels_x_mul_y R hd
    rw [← hh (Units.mk0 (1 + s * t) hd), Units.val_mk0]
    exact h
  · intro s t hd
    have hs : s ≠ 0 := by
      rintro rfl
      simp at hd
    refine ⟨Units.mk0 s hs, -s, ?_⟩
    rw [← hh (Units.mk0 s hs), Units.val_mk0]
    exact omq_rankOneRels_x_mul_y_singular R hd

end CFSG.LocalAnalysis.WeakClosure81
