module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3Defs
public import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3UnitaryInv
public import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3UnitaryCenter
public import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3UnitaryCard
public import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3UnitaryGen

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped Pointwise

section Unitary

variable {m : ℕ} {F' : Type} [Field F']

theorem model3_unitary_a (hF' : UnitaryFieldData 2 m F') :
    Model3TildeA ↥(unitarySU 2 m F' 3) (2 ^ m) := by
  intro R
  obtain ⟨L, hL, hZ, -⟩ := model3_unitary_center_eq_point hF' R
  obtain ⟨hcard, hsq⟩ := model3_unitary_card_point hF' hL
  refine ⟨?_, fun z hz => ?_⟩
  · rw [← hcard, ← hZ]
    exact (Subgroup.card_map_of_injective (R : Subgroup ↥(unitarySU 2 m F' 3)).subtype_injective).symm
  · have hzT : ((z : ↥(R : Subgroup ↥(unitarySU 2 m F' 3))) : ↥(unitarySU 2 m F' 3)) ∈
        isotropicTransvectionGroup hF' 3 L := by
      rw [← hZ]
      exact ⟨z, hz, rfl⟩
    exact Subtype.ext (hsq _ hzT)

theorem model3_unitary_b (hF' : UnitaryFieldData 2 m F') :
    Model3TildeB ↥(unitarySU 2 m F' 3) := by
  haveI := hF'.finite
  intro R x hx
  have hxP : IsPGroup 2 (Subgroup.zpowers x) := by
    intro y
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp y.2
    refine ⟨1, Subtype.ext ?_⟩
    change (y : ↥(unitarySU 2 m F' 3)) ^ 2 ^ 1 = 1
    rw [← hk, pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, sq, hx,
      one_zpow]
  obtain ⟨R', hR'⟩ := hxP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥(unitarySU 2 m F' 3) R R'
  have hxR' : x ∈ (R' : Subgroup ↥(unitarySU 2 m F' 3)) := hR' (Subgroup.mem_zpowers x)
  rw [← hg] at hxR'
  obtain ⟨r, hr, hrx⟩ := Subgroup.mem_smul_pointwise_iff_exists _ _ _ |>.mp hxR'
  have hxr : x = g * r * g⁻¹ := by rw [← hrx]; rfl
  have hr2 : r * r = 1 := by
    have : g * (r * r) * g⁻¹ = 1 := by
      calc g * (r * r) * g⁻¹ = (g * r * g⁻¹) * (g * r * g⁻¹) := by group
        _ = x * x := by rw [← hxr]
        _ = 1 := hx
    simpa using this
  have hrc := model3_unitary_involution_central hF' R ⟨r, hr⟩ (Subtype.ext hr2)
  refine ⟨g, ⟨⟨r, hr⟩, hrc, ?_⟩⟩
  change r = g⁻¹ * x * g
  rw [hxr]
  group

theorem model3_unitary_c (hm : 2 ≤ m) (hF' : UnitaryFieldData 2 m F') :
    Model3TildeC ↥(unitarySU 2 m F' 3) := by
  intro R τ hτ
  obtain ⟨L, hL, hZ, hfix⟩ := model3_unitary_center_eq_point hF' R
  by_cases hLτ : τ⁻¹ • L = L
  · exfalso
    apply hτ
    have hconj : ((center ↥(R : Subgroup ↥(unitarySU 2 m F' 3))).map
        (R : Subgroup ↥(unitarySU 2 m F' 3)).subtype).map (MulAut.conj τ⁻¹).toMonoidHom =
        (center ↥(R : Subgroup ↥(unitarySU 2 m F' 3))).map
          (R : Subgroup ↥(unitarySU 2 m F' 3)).subtype := by
      rw [hZ, (unitary_point_conjugation hF' τ⁻¹ hL).2.1, hLτ]
    rw [hconj, sup_idem]
    exact R.isPGroup'.to_le (Subgroup.map_subtype_le _)
  · exact model3_unitary_generation hm hF' R hL hZ hfix τ hLτ

theorem model3_unitary (hm : 2 ≤ m) (hF' : UnitaryFieldData 2 m F') :
    Model3Tilde ↥(unitarySU 2 m F' 3) (2 ^ m) :=
  ⟨model3_unitary_a hF', model3_unitary_b hF', model3_unitary_c hm hF'⟩

end Unitary

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
