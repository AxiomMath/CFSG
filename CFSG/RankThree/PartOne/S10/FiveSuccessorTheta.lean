module

import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.GroupTheory.ThetaComponents

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

theorem subgroupOf_mem_thetaComponents_of_le (hp : p.Prime) {X Y' Y : Subgroup G}
    (hXY' : X ≤ Y') (hY'Y : Y' ≤ Y) (hX : X.subgroupOf Y ∈ thetaComponents p ↥Y) :
    X.subgroupOf Y' ∈ thetaComponents p ↥Y' := by
  set e : X.subgroupOf Y ≃* X.subgroupOf Y' :=
    (Subgroup.subgroupOfEquivOfLe (hXY'.trans hY'Y)).trans (Subgroup.subgroupOfEquivOfLe hXY').symm
  refine ⟨?_, ?_, ?_⟩
  · have := hX.1
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  · have h := hX.2.1.comap (Subgroup.inclusion hY'Y)
    rwa [Subgroup.comap_inclusion_subgroupOf] at h
  · exact LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr _ _ e (aschbacherSolvableCore_map_mulEquiv hp e)) hX.2.2

theorem map_mem_thetaComponents_subgroupOf_of_map_eq (hp : p.Prime) {X₁ : Subgroup G}
    {Z : Subgroup X₁} {M : Subgroup G} (hZ : Z.map X₁.subtype = M) {T : Subgroup Z}
    (hT : T ∈ thetaComponents p Z) :
    (T.map Z.subtype).map X₁.subtype ≤ M ∧
      ((T.map Z.subtype).map X₁.subtype).subgroupOf M ∈ thetaComponents p ↥M := by
  set e : Z ≃* M :=
    (Z.equivMapOfInjective X₁.subtype X₁.subtype_injective).trans (MulEquiv.subgroupCongr hZ)
  have he : ∀ z : Z, ((e z : M) : G) = (((z : X₁)) : G) := fun _ => rfl
  have himg : (T.map e.toMonoidHom).map M.subtype = (T.map Z.subtype).map X₁.subtype := by
    rw [Subgroup.map_map, Subgroup.map_map]
    exact congrArg (Subgroup.map · T) (MonoidHom.ext he)
  refine ⟨himg ▸ Subgroup.map_subtype_le _, ?_⟩
  rw [← himg, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  exact map_mulEquiv_mem_thetaComponents hp e hT

end CFSG.RankThree.PartOne
