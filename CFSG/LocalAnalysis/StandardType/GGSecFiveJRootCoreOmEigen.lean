module

import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.StandardType

theorem jcoreOm_eigen_iff {ι F : Type} [Field F] {x : (ι → F) ≃ₗ[F] (ι → F)} {w : ι → F}
    (hxa : ∀ v c, x v c = w c * v c) (μ : F) (v : ι → F) :
    x v = μ • v ↔ ∀ c, w c ≠ μ → v c = 0 := by
  constructor
  · intro h c hc
    have h1 := congrFun h c
    rw [hxa, Pi.smul_apply, smul_eq_mul] at h1
    have h2 : (w c - μ) * v c = 0 := by rw [sub_mul, h1, sub_self]
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hc)
  · intro h
    funext c
    rw [hxa, Pi.smul_apply, smul_eq_mul]
    by_cases hc : w c = μ
    · rw [hc]
    · rw [h c hc, mul_zero, mul_zero]

theorem jcoreOm_eigen_eq_span {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {x : (ι → F) ≃ₗ[F] (ι → F)} {w : ι → F} (hxa : ∀ v c, x v c = w c * v c) (μ : F)
    {W : Submodule F (ι → F)} (hW : ∀ v, v ∈ W ↔ x v = μ • v) :
    W = Submodule.span F (Set.range fun c : {c // w c = μ} => (Pi.single c.1 1 : ι → F)) := by
  apply le_antisymm
  · intro v hv
    have h0 := (jcoreOm_eigen_iff hxa μ v).mp ((hW v).mp hv)
    rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ fun c _ => ?_
    by_cases hc : w c = μ
    · have hs : (Pi.single c (v c) : ι → F) = v c • Pi.single c 1 := by
        funext b
        by_cases hbc : b = c
        · subst hbc
          simp
        · simp [Pi.single_eq_of_ne hbc]
      rw [hs]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨c, hc⟩, rfl⟩)
    · rw [h0 c hc, Pi.single_zero]
      exact zero_mem _
  · rw [Submodule.span_le]
    rintro _ ⟨⟨c, hc⟩, rfl⟩
    refine (hW _).mpr ((jcoreOm_eigen_iff hxa μ _).mpr fun b hb => ?_)
    have hbc : b ≠ c := by
      rintro rfl
      exact hb hc
    exact Pi.single_eq_of_ne hbc 1

theorem jcoreOm_finrank_eigen {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {x : (ι → F) ≃ₗ[F] (ι → F)} {w : ι → F} (hxa : ∀ v c, x v c = w c * v c) (μ : F)
    {W : Submodule F (ι → F)} (hW : ∀ v, v ∈ W ↔ x v = μ • v) :
    Module.finrank F W = Nat.card {c // w c = μ} := by
  classical
  have hli : LinearIndependent F (fun c : {c // w c = μ} => (Pi.single c.1 1 : ι → F)) := by
    have h := (Pi.basisFun F ι).linearIndependent.comp (Subtype.val : {c // w c = μ} → ι)
      Subtype.val_injective
    convert h using 1
    funext c
    simp [Pi.basisFun_apply]
  rw [jcoreOm_eigen_eq_span hxa μ hW, finrank_span_eq_card hli, Nat.card_eq_fintype_card]

end CFSG.StandardType

end
