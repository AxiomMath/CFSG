module

public import CFSG.Timmesfeld.RootSubgroupReduction
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

@[expose] def RootClosure (D : Set G) : Prop :=
  ∀ d ∈ D, ∀ a ∈ rootSet D d, ∀ b ∈ rootSet D d, a ≠ b → a * b ∈ rootSet D d

theorem one_notMem_rootSet (hD : IsRootInvolutionSet D) (d : G) : (1 : G) ∉ rootSet D d :=
  fun h => hD.ne_one h.1 rfl

theorem coe_rootGroup_of_rootClosure (hD : IsRootInvolutionSet D) (hc : RootClosure D) {d : G}
    (hd : d ∈ D) : (rootGroup D d : Set G) = insert 1 (rootSet D d) := by
  obtain ⟨A, hA, -⟩ := exists_rootSubgroup_of_closed hD (hc d hd)
  have h1 : rootGroup D d ≤ A := by
    rw [rootGroup, Subgroup.closure_le, hA]
    exact Set.subset_insert 1 _
  have h2 : A ≤ rootGroup D d := by
    intro x hx
    rw [← SetLike.mem_coe, hA] at hx
    rcases hx with rfl | hx
    · exact (rootGroup D d).one_mem
    · exact rootSet_subset_rootGroup D d hx
  rw [le_antisymm h1 h2, hA]

theorem mem_rootGroup_iff_of_rootClosure (hD : IsRootInvolutionSet D) (hc : RootClosure D)
    {d g : G} (hd : d ∈ D) : g ∈ rootGroup D d ↔ g = 1 ∨ g ∈ rootSet D d := by
  rw [← SetLike.mem_coe, coe_rootGroup_of_rootClosure hD hc hd]
  rfl

theorem mem_rootSet_iff_mem_rootGroup_of_rootClosure (hD : IsRootInvolutionSet D)
    (hc : RootClosure D) {d g : G} (hd : d ∈ D) : g ∈ rootSet D d ↔ g ∈ rootGroup D d ∧ g ≠ 1 := by
  rw [mem_rootGroup_iff_of_rootClosure hD hc hd]
  constructor
  · intro hg
    exact ⟨Or.inr hg, fun h => one_notMem_rootSet hD d (h ▸ hg)⟩
  · rintro ⟨hg | hg, hne⟩
    · exact absurd hg hne
    · exact hg

theorem card_rootGroup_of_rootClosure [Finite G] (hD : IsRootInvolutionSet D)
    (hc : RootClosure D) {d : G} (hd : d ∈ D) :
    Nat.card (rootGroup D d) = (rootSet D d).ncard + 1 := by
  rw [← SetLike.coe_sort_coe, coe_rootGroup_of_rootClosure hD hc hd, Nat.card_coe_set_eq,
    Set.ncard_insert_of_notMem (one_notMem_rootSet hD d) (Set.toFinite _)]

theorem exists_card_rootGroup_eq_two_pow [Finite G] (hD : IsRootInvolutionSet D) {d : G}
    (hd : d ∈ D) : ∃ m : ℕ, Nat.card (rootGroup D d) = 2 ^ m :=
  IsPGroup.iff_card.mp (isPGroup_rootGroup hD hd)

theorem card_rootGroup_eq [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hc : RootClosure D) {d e : G} (hd : d ∈ D) (he : e ∈ D) :
    Nat.card (rootGroup D e) = Nat.card (rootGroup D d) := by
  rw [card_rootGroup_of_rootClosure hD hc hd, card_rootGroup_of_rootClosure hD hc he,
    ncard_rootSet_eq hclass hd he]

theorem rootGroup_inf_eq_bot_of_rootClosure (hD : IsRootInvolutionSet D) (hc : RootClosure D)
    {d e : G} (hd : d ∈ D) (he : e ∈ D) (hne : rootSet D d ≠ rootSet D e) :
    rootGroup D d ⊓ rootGroup D e = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  rcases (mem_rootGroup_iff_of_rootClosure hD hc hd).1 (Subgroup.mem_inf.1 hg).1 with h | hgd
  · exact h
  rcases (mem_rootGroup_iff_of_rootClosure hD hc he).1 (Subgroup.mem_inf.1 hg).2 with h | hge
  · exact h
  exact absurd ((rootSet_eq_of_mem hgd).symm.trans (rootSet_eq_of_mem hge)) hne

theorem Hyp.exists_rootSubgroup (h : Hyp G D) (hc : RootClosure D) {d : G} (hd : d ∈ D) :
    ∃ A : Subgroup G, (A : Set G) = insert 1 (rootSet D d) ∧ ∀ a ∈ A, a * a = 1 :=
  exists_rootSubgroup_of_closed h.root (hc d hd)

end CFSG.Timmesfeld
