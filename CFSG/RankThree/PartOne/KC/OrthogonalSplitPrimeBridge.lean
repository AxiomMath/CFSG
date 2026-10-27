module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.Classical2.OrthogonalIsotropicUnipotent
public import CFSG.RankThree.PartOne.KC.OrthogonalDerivedCentralizer
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedBlocks

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
open scoped commutatorElement

section Bridge

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem orthDerived_le_orthogonalGroup' :
    orthDerived Q ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
    (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)

theorem map_subgroupOf_isometryCentralizer (x : V ≃ₗ[K] V) :
    ((isometryCentralizer Q x).subgroupOf (orthDerived Q)).map (orthDerived Q).subtype =
      orthDerived Q ⊓ Subgroup.centralizer {x} := by
  rw [Subgroup.subgroupOf_map_subtype]
  ext g
  simp only [isometryCentralizer, Subgroup.mem_inf]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨orthDerived_le_orthogonalGroup' h.1, h.2⟩, h.1⟩⟩

theorem map_commutator_subgroupOf_isometryCentralizer (x : V ≃ₗ[K] V) :
    (⁅(isometryCentralizer Q x).subgroupOf (orthDerived Q),
        (isometryCentralizer Q x).subgroupOf (orthDerived Q)⁆).map (orthDerived Q).subtype =
      derivedCentralizer (orthDerived Q) x := by
  rw [Subgroup.map_commutator, map_subgroupOf_isometryCentralizer]
  rfl

theorem iSup_commutator_isometryCentralizer_eq_top (Ã : Subgroup (orthDerived Q))
    (h : (⨆ (x : V ≃ₗ[K] V) (_ : x ∈ Ã.map (orthDerived Q).subtype ∧ x ≠ 1),
        derivedCentralizer (orthDerived Q) x) = orthDerived Q) :
    (⨆ (x : orthDerived Q) (_ : x ∈ Ã ∧ x ≠ 1),
        ⁅(isometryCentralizer Q (x : V ≃ₗ[K] V)).subgroupOf (orthDerived Q),
          (isometryCentralizer Q (x : V ≃ₗ[K] V)).subgroupOf (orthDerived Q)⁆) = ⊤ := by
  apply Subgroup.map_injective (orthDerived Q).subtype_injective
  rw [Subgroup.map_iSup]
  simp only [Subgroup.map_iSup, map_commutator_subgroupOf_isometryCentralizer, Subgroup.map_top,
    Subgroup.range_subtype]
  refine Eq.trans ?_ h
  refine le_antisymm (iSup_le fun x => iSup_le fun hx => ?_)
    (iSup_le fun y => iSup_le fun hy => ?_)
  · exact le_iSup₂_of_le (x : V ≃ₗ[K] V)
      ⟨⟨x, hx.1, rfl⟩, fun h1 => hx.2 (Subtype.ext h1)⟩ le_rfl
  · obtain ⟨⟨x, hxÃ, rfl⟩, hy1⟩ := hy
    exact le_iSup₂_of_le x ⟨hxÃ, fun h1 => hy1 (by rw [h1]; rfl)⟩ le_rfl

end Bridge

end CFSG.RankThree.PartOne.KCOrthogonal
