module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerSubgroupCyclic
public import Mathlib.GroupTheory.Complement
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Lifting a normal complement from a subgroup type
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- A normal complement to the internal normalizer of `X.subgroupOf D`
lifts to the ambient subgroup equality used in the Section 4 bad-fibre
contract. -/
public theorem ambient_normalComplement_of_subgroupOf
    {G : Type u} [Group G] [Finite G]
    (D X : Subgroup G) (hXleD : X ≤ D)
    (Q : Subgroup D) (hQnormal : Q.Normal)
    (hcomp : Q.IsComplement'
      (Subgroup.normalizer (X.subgroupOf D : Set D))) :
    let QA : Subgroup G := Q.map D.subtype
    IsNormalIn QA D ∧
      D = QA ⊔ (D ⊓ Subgroup.normalizer (X : Set G)) ∧
      QA ⊓ (D ⊓ Subgroup.normalizer (X : Set G)) = ⊥ ∧
      Nat.card QA = Nat.card Q := by
  let QA : Subgroup G := Q.map D.subtype
  let ND : Subgroup D :=
    Subgroup.normalizer (X.subgroupOf D : Set D)
  have hNDmap : ND.map D.subtype =
      D ⊓ Subgroup.normalizer (X : Set G) := by
    rw [show ND = (D ⊓ Subgroup.normalizer (X : Set G)).subgroupOf D by
      exact normalizer_subgroupOf_eq_subgroupOf_inf_normalizer D X hXleD]
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_left]
  have hQnormalAmbient : IsNormalIn QA D := by
    refine ⟨Subgroup.map_subtype_le Q, ?_⟩
    intro d hd q hq
    rcases Subgroup.mem_map.mp hq with ⟨qD, hqD, rfl⟩
    let dD : D := ⟨d, hd⟩
    have hconj : dD * qD * dD⁻¹ ∈ Q :=
      hQnormal.conj_mem qD hqD dD
    exact Subgroup.mem_map.mpr ⟨dD * qD * dD⁻¹, hconj, rfl⟩
  have hsupmap := congrArg (fun H : Subgroup D => H.map D.subtype)
    hcomp.sup_eq_top
  have hsup : D = QA ⊔ (D ⊓ Subgroup.normalizer (X : Set G)) := by
    have hsup' : QA ⊔ (D ⊓ Subgroup.normalizer (X : Set G)) = D := by
      rw [Subgroup.map_sup, hNDmap,
        ← MonoidHom.range_eq_map D.subtype, Subgroup.range_subtype D] at hsupmap
      exact hsupmap
    exact hsup'.symm
  have hdisjMap : Disjoint QA
      (D ⊓ Subgroup.normalizer (X : Set G)) := by
    have h := Subgroup.disjoint_map D.subtype_injective hcomp.disjoint
    simpa [QA, ND, hNDmap] using h
  have hcard : Nat.card QA = Nat.card Q := by
    dsimp [QA]
    rw [Subgroup.card_map_of_injective D.subtype_injective]
  exact ⟨hQnormalAmbient, hsup, hdisjMap.eq_bot, hcard⟩

end CFSG.GorensteinWalter
