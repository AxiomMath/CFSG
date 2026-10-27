module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving

open scoped commutatorElement

theorem isPerfect_of_simple_nonabelian (G : Type) [Group G] [IsSimpleGroup G]
    (h : ∃ a b : G, a * b ≠ b * a) : Group.IsPerfect G := by
  refine Group.isPerfect_def.mpr ?_
  rcases (Subgroup.commutator_normal (⊤ : Subgroup G) ⊤).eq_bot_or_eq_top with hb | ht
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    have hm : ⁅a, b⁆ ∈ commutator G :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [commutator_def, hb, Subgroup.mem_bot] at hm
    exact hab (commutatorElement_eq_one_iff_mul_comm.1 hm)
  · rw [commutator_def]
    exact ht

theorem isPerfect_of_simple_not_prime_card (G : Type) [Group G] [IsSimpleGroup G]
    (h : ¬ (Nat.card G).Prime) : Group.IsPerfect G := by
  refine isPerfect_of_simple_nonabelian G ?_
  by_contra hc
  push Not at hc
  have : IsMulCommutative G := ⟨⟨fun a b => hc a b⟩⟩
  exact h (Group.is_simple_iff_prime_card.mp ‹IsSimpleGroup G›)

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving
