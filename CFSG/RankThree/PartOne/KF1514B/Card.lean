module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.RankThree.PartOne.KF1514B

variable {G : Type*} [Group G] [Finite G] {Q : Type*} [Group Q]

theorem card_le_ker_mul_map (φ : G →* Q) (H : Subgroup G) :
    Nat.card H ≤ Nat.card ↥(H ⊓ φ.ker) * Nat.card ↥(H.map φ) := by
  have h := Subgroup.card_ker_mul_card_range (φ.comp H.subtype)
  have hr : (φ.comp H.subtype).range = H.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hr] at h
  have hk : Nat.card (φ.comp H.subtype).ker ≤ Nat.card ↥(H ⊓ φ.ker) := by
    refine Nat.card_le_card_of_injective (fun x => ⟨(x.1 : G), x.1.2, ?_⟩) ?_
    · exact MonoidHom.mem_ker.2 (by simpa only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype] using x.2)
    · intro x y hxy
      have h2 := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext h2)
  rw [← h]
  exact Nat.mul_le_mul_right _ hk

theorem card_inf_le_mul_map (N H : Subgroup G) (φ : ↥N →* Q) :
    Nat.card ↥(H ⊓ N) ≤ Nat.card ↥(H ⊓ φ.ker.map N.subtype) *
      Nat.card ↥((H.subgroupOf N).map φ) := by
  have h := Subgroup.card_ker_mul_card_range (φ.comp (H.subgroupOf N).subtype)
  have hr : (φ.comp (H.subgroupOf N).subtype).range = (H.subgroupOf N).map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hr] at h
  have h1 : Nat.card ↥(H ⊓ N) ≤ Nat.card ↥(H.subgroupOf N) := by
    refine Nat.card_le_card_of_injective
      (fun x => (⟨⟨(x : G), x.2.2⟩, x.2.1⟩ : ↥(H.subgroupOf N))) ?_
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : ↥(H.subgroupOf N) => ((z : ↥N) : G)) hxy
  have hk : Nat.card (φ.comp (H.subgroupOf N).subtype).ker ≤
      Nat.card ↥(H ⊓ φ.ker.map N.subtype) := by
    refine Nat.card_le_card_of_injective
      (fun x => ⟨(((x.1 : ↥(H.subgroupOf N)) : ↥N) : G), x.1.2, ?_⟩) ?_
    · refine ⟨((x.1 : ↥(H.subgroupOf N)) : ↥N), ?_, rfl⟩
      exact MonoidHom.mem_ker.2 (by simpa only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype] using x.2)
    · intro x y hxy
      have h2 := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext (Subtype.ext h2))
  calc Nat.card ↥(H ⊓ N) ≤ Nat.card ↥(H.subgroupOf N) := h1
    _ = Nat.card (φ.comp (H.subgroupOf N).subtype).ker *
        Nat.card ↥((H.subgroupOf N).map φ) := h.symm
    _ ≤ _ := Nat.mul_le_mul_right _ hk

end CFSG.RankThree.PartOne.KF1514B
