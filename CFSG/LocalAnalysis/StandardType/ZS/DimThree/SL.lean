module

public import CFSG.LocalAnalysis.StandardType.ZS.DimThree.Basic
public import CFSG.Open.StatedDefs
import CFSG.RankThree.PartOne.N1322.CaseBasic
import CFSG.RankThree.PartOne.N1322.CoreHyp

public section

namespace CFSG.StandardType.ZS.DimThree

open Subgroup CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.LIT (autGL)

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private lemma det_eq_pm_one_of_mem_zt (hp : p ≠ 2) (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hR : ReflGen p A) :
    ∀ g ∈ A, LinearEquiv.det g = 1 ∨ LinearEquiv.det g = -1 := by
  intro g hg
  rw [hR] at hg
  refine Subgroup.closure_induction
    (p := fun g _ => LinearEquiv.det g = 1 ∨ LinearEquiv.det g = -1) ?_ ?_ ?_ ?_ hg
  · intro x hx
    have hmat : N1322.IsRefl (autGL e x) := (isRefl_iff_autGL hp e x).mp hx.2
    have h1 : (LinearEquiv.det x : ZMod p) = -1 := by
      rw [← det_autGL e x]
      exact N1322.IsRefl.det_eq hmat
    have h2 : LinearEquiv.det x = -1 := by
      apply Units.ext
      rw [Units.val_neg, Units.val_one]
      exact h1
    exact Or.inr h2
  · exact Or.inl (map_one _)
  · intro x y _ _ hx hy
    rw [map_mul]
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> simp [hx, hy]
  · intro x _ hx
    rw [map_inv]
    rcases hx with hx | hx <;> simp [hx]

theorem mem_iff_det_of_statedSL_le (hp : p ≠ 2) (e : U ≃ₗ[ZMod p] (Fin 3 → ZMod p))
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hR : ReflGen p A) (hI : AbsIrred p A)
    (hSL : CFSG.Open.StatedSL 3 (ZMod p) ≤ A.map (autGL e).toMonoidHom) :
    ∀ g : U ≃ₗ[ZMod p] U, g ∈ A ↔ (LinearEquiv.det g = 1 ∨ LinearEquiv.det g = -1) := by
  have hdet := det_eq_pm_one_of_mem_zt hp e hR
  have hdetOne : ∀ g, LinearEquiv.det g = 1 → g ∈ A := by
    intro g hg
    have hmat : ((autGL e g : GL (Fin 3) (ZMod p)) :
        Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1 := by
      rw [det_autGL]
      simpa using congrArg Units.val hg
    have hmemG : autGL e g ∈ A.map (autGL e).toMonoidHom :=
      hSL (Subgroup.subset_closure hmat)
    simpa using (Subgroup.mem_map_equiv (f := autGL e)).mp hmemG
  have hdetNeg : ∀ g, LinearEquiv.det g = -1 → g ∈ A := by
    intro g hg
    obtain ⟨t₀, ht₀G, ht₀r⟩ := exists_isRefl_mem hp e hR hI
    have htA : (autGL e).symm t₀ ∈ A := (Subgroup.mem_map_equiv (f := autGL e)).mp ht₀G
    have htDet : LinearEquiv.det ((autGL e).symm t₀) = -1 := by
      apply Units.ext
      have h1 : ((autGL e ((autGL e).symm t₀) : GL (Fin 3) (ZMod p)) :
          Matrix (Fin 3) (Fin 3) (ZMod p)).det = -1 := by
        rw [MulEquiv.apply_symm_apply]
        exact N1322.IsRefl.det_eq ht₀r
      rw [det_autGL] at h1
      rwa [Units.val_neg, Units.val_one]
    have htg : (autGL e).symm t₀ * g ∈ A := by
      apply hdetOne
      rw [map_mul, htDet, hg, neg_mul_neg, one_mul]
    have hgA : ((autGL e).symm t₀)⁻¹ * ((autGL e).symm t₀ * g) ∈ A :=
      A.mul_mem (A.inv_mem htA) htg
    simpa using hgA
  exact fun g => ⟨fun hg => hdet g hg, fun hg => hg.elim (hdetOne g) (hdetNeg g)⟩

end CFSG.StandardType.ZS.DimThree
