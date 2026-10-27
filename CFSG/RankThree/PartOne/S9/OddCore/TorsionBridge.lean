module

public import CFSG.Foundations.Basic

public section

namespace CFSG.RankThree.PartOne.Torsion37

open CFSG Subgroup

theorem center_map_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (center G).map e.toMonoidHom = center H := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_center_iff,
    Subgroup.mem_center_iff]
  constructor
  · intro hx g
    obtain ⟨g, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hx]
  · intro hx g
    apply e.injective
    rw [map_mul, map_mul, hx]

theorem frattini_map_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (frattini G).map e.toMonoidHom = frattini H :=
  OrderIso.map_radical (MulEquiv.mapSubgroup e)

theorem isExtraspecialPGroup_of_mulEquiv {p : ℕ} {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : IsExtraspecialPGroup p G) : IsExtraspecialPGroup p H := by
  obtain ⟨hp, hcomm, hfrat, hcard⟩ := h
  have hc : (commutator G).map e.toMonoidHom = commutator H := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  refine ⟨hp.of_equiv e, ?_, ?_, ?_⟩
  · rw [← hc, hcomm, center_map_mulEquiv]
  · rw [← frattini_map_mulEquiv e, hfrat, center_map_mulEquiv]
  · rw [← center_map_mulEquiv e, Subgroup.card_map_of_injective e.injective, hcard]

variable {G G' : Type} [Group G] [Group G']

theorem inSubgroup_center_map (f : G →* G') (hf : Function.Injective f) (K : Subgroup G) :
    inSubgroup Subgroup.center (K.map f) = (inSubgroup Subgroup.center K).map f := by
  unfold inSubgroup
  rw [← center_map_mulEquiv (K.equivMapOfInjective f hf), Subgroup.map_map, Subgroup.map_map]
  rfl

theorem inSubgroup_frattini_map (f : G →* G') (hf : Function.Injective f) (K : Subgroup G) :
    inSubgroup frattini (K.map f) = (inSubgroup frattini K).map f := by
  unfold inSubgroup
  rw [← frattini_map_mulEquiv (K.equivMapOfInjective f hf), Subgroup.map_map, Subgroup.map_map]
  rfl

end CFSG.RankThree.PartOne.Torsion37
