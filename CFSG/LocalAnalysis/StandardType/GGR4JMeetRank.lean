module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggR4Meet_of_rank {G : Type} [Group G] [Finite G] {Bs L J : Subgroup G} (hJL : J ≤ L)
    (hE4 : Nat.card ((Bs ⊓ L).subgroupOf L) = 3 ^ 4)
    (hrank : Nat.card ((Bs ⊓ L).subgroupOf L) ≤
      3 * Nat.card ((Bs ⊓ L).subgroupOf L ⊓ J.subgroupOf L : Subgroup ↥L)) :
    3 ^ 3 ≤ Nat.card (Bs ⊓ J : Subgroup G) := by
  have hinf : ((Bs ⊓ L).subgroupOf L ⊓ J.subgroupOf L : Subgroup ↥L) =
      (Bs ⊓ J).subgroupOf L := by
    rw [Subgroup.inf_subgroupOf_right]
    exact (Subgroup.comap_inf Bs J L.subtype).symm
  have hcard : Nat.card ((Bs ⊓ L).subgroupOf L ⊓ J.subgroupOf L : Subgroup ↥L) =
      Nat.card (Bs ⊓ J : Subgroup G) := by
    rw [hinf]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (show Bs ⊓ J ≤ L from inf_le_right.trans hJL)).toEquiv
  have h1 : 81 ≤ 3 * Nat.card (Bs ⊓ J : Subgroup G) := by
    have h : 3 ^ 4 ≤ 3 * Nat.card (Bs ⊓ J : Subgroup G) := by
      rw [← hcard]
      rw [← hE4]
      exact hrank
    norm_num at h ⊢
    exact h
  have h2 : 27 ≤ Nat.card (Bs ⊓ J : Subgroup G) := by omega
  norm_num
  exact h2

end CFSG.StandardType

end
