module

public import CFSG.RankThree.GF2n.Stroth78.Basic

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a
open CFSG.LargeExtraspecial.Timmesfeld (Qa)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

abbrev Hbar (z : G) : Type := ↥(H z) ⧸ (Q z).subgroupOf (H z)

abbrev QaOf (a : G) : Subgroup G := Qa a

abbrev La (S : Setting z E F) (a : G) : Subgroup G := Q z ⊔ (QaOf a ⊓ H z)

abbrev Ra (S : Setting z E F) (a : G) : Subgroup G := Q z ⊔ (centerIn (QaOf a) ⊓ H z)

theorem Q_le_La (S : Setting z E F) (a : G) : Q z ≤ La S a := le_sup_left

@[expose] noncomputable def Lbar (S : Setting z E F) (a : G) : Subgroup (Hbar z) :=
  ((La S a).subgroupOf (H z)).map (QuotientGroup.mk' ((Q z).subgroupOf (H z)))

@[expose] noncomputable def Rbar (S : Setting z E F) (a : G) : Subgroup (Hbar z) :=
  ((Ra S a).subgroupOf (H z)).map (QuotientGroup.mk' ((Q z).subgroupOf (H z)))

theorem one_mem_Lbar (S : Setting z E F) (a : G) : (1 : Hbar z) ∈ Lbar S a := by
  refine Subgroup.mem_map.mpr ⟨1, ?_, rfl⟩
  exact Subgroup.mem_subgroupOf.mpr (Q_le_La S a (one_mem _))

@[expose] def IsA2Q (S : Setting z E F) (x : G) : Prop :=
  x ∈ H z ∧ x ∉ Q z ∧ x ^ 2 ∈ Q z ∧
    Nat.card ↥(⁅Q z, Subgroup.zpowers x⁆ ⊔ ZQ z) = 4 * Nat.card (ZQ z) ∧
    IsElemAbelian 2 ⁅Q z, Subgroup.zpowers x⁆

@[expose] def IsA2Hbar (S : Setting z E F) (α : Hbar z) : Prop :=
  ∃ x : ↥(H z), QuotientGroup.mk x = α ∧ IsA2Q S (x : G)

@[expose] def Tset (S : Setting z E F) (a : G) : Set (Hbar z) :=
  {α | α ∈ Lbar S a ∧ α ≠ 1 ∧ IsA2Hbar S α}

@[expose] def Eset (S : Setting z E F) (a : G) : Set (Hbar z) :=
  {α | ∃ h : Hbar z, ∃ β ∈ Tset S a, α = h * β * h⁻¹}

@[expose] noncomputable def Xsub (S : Setting z E F) (a : G) : Subgroup (Hbar z) :=
  Subgroup.closure (Eset S a)

theorem subset_Xsub (S : Setting z E F) (a : G) : Eset S a ⊆ Xsub S a :=
  fun _ h => Subgroup.subset_closure h

end CFSG.RankThree.GF2n.Stroth78
