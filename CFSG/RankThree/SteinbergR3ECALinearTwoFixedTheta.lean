module

public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearTwoAutomorphism
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearTwoDescentField
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCSubfieldCentralizer
public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore

public section

namespace CFSG.RankThree.LinearTwo

open CFSG.RankThree.LocalRank CFSG.ComponentClassification.CatalogueSchreierLinearTwo
open CFSG.ComponentClassification.CatalogueBLinearTwoDescent (fixedSubfield)
open CFSG.ComponentClassification.UnbalancedGS.SubfieldCentralizer (subfieldD)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  (linear_two_automorphism_semilinear_isomorphism)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel projectiveSpecialLinearGroupEquivStatedProj)
open CFSG.LinearGroups (linear_projective_simple)

section Coordinates

variable {K : Type} [Field K] [Finite K]

theorem conj_mem_coordinateG_of_mem_coordinateD {h y : Equiv.Perm (Omega K)}
    (hh : h ∈ coordinateD K) (hy : y ∈ coordinateG K) : h * y * h⁻¹ ∈ coordinateG K := by
  have := (coordinateG_normal_in_D K).conj_mem ⟨y, coordinateG_le_D K hy⟩
    (Subgroup.mem_subgroupOf.mpr hy) ⟨h, hh⟩
  rw [Subgroup.mem_subgroupOf] at this
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using this

theorem coordinateG_inf_centralizer_conj {h : Equiv.Perm (Omega K)} (hh : h ∈ coordinateD K)
    (x : Equiv.Perm (Omega K)) :
    coordinateG K ⊓ Subgroup.centralizer {h * x * h⁻¹} =
      (coordinateG K ⊓ Subgroup.centralizer {x}).map (MulAut.conj h).toMonoidHom := by
  ext y
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_map,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨hyG, hyx⟩
    refine ⟨h⁻¹ * y * h, ⟨?_, ?_⟩, by group⟩
    · simpa only [inv_inv] using conj_mem_coordinateG_of_mem_coordinateD (inv_mem hh) hyG
    · calc h⁻¹ * y * h * x = h⁻¹ * (y * (h * x * h⁻¹)) * h := by group
        _ = h⁻¹ * ((h * x * h⁻¹) * y) * h := by rw [hyx]
        _ = x * (h⁻¹ * y * h) := by group
  · rintro ⟨z, ⟨hzG, hzx⟩, rfl⟩
    refine ⟨conj_mem_coordinateG_of_mem_coordinateD hh hzG, ?_⟩
    calc h * z * h⁻¹ * (h * x * h⁻¹) = h * (z * x) * h⁻¹ := by group
      _ = h * (x * z) * h⁻¹ := by rw [hzx]
      _ = h * x * h⁻¹ * (h * z * h⁻¹) := by group

end Coordinates

end CFSG.RankThree.LinearTwo
