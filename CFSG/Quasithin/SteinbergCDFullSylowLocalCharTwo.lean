module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.QuasithinDefs

public section

namespace CFSG.Quasithin.SteinbergCD

open Subgroup CFSG.Assembly.Quasithin

theorem eq_of_perfect_of_two_group_quotient {G : Type*} [Group G] [Finite G] {L N : Subgroup G}
    (hLp : ⁅L, L⁆ = L) (hNL : N ≤ L) (hNn : (N.subgroupOf L).Normal)
    (h2 : ∀ x ∈ L, ∃ k : ℕ, x ^ 2 ^ k ∈ N) : N = L := by
  have hQ2 : IsPGroup 2 (L ⧸ N.subgroupOf L) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := h2 x x.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
    exact hk
  have : Group.IsPerfect L := Subgroup.isPerfect_iff.mpr hLp
  have : Group.IsPerfect (L ⧸ N.subgroupOf L) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have : Group.IsNilpotent (L ⧸ N.subgroupOf L) := hQ2.isNilpotent
  have hsub : Subsingleton (L ⧸ N.subgroupOf L) := by
    rcases subsingleton_or_nontrivial (L ⧸ N.subgroupOf L) with h | h
    · exact h
    · exact (Group.IsPerfect.not_isSolvable (L ⧸ N.subgroupOf L) inferInstance).elim
  refine le_antisymm hNL fun x hx => ?_
  have h1 : (QuotientGroup.mk (⟨x, hx⟩ : L) : L ⧸ N.subgroupOf L) = 1 := Subsingleton.elim _ _
  rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
  exact h1

end SteinbergCD

open Subgroup CFSG.Assembly.Quasithin SteinbergCD

end CFSG.Quasithin
