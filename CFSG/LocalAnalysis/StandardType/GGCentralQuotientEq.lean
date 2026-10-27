module

public import CFSG.LocalAnalysis.ComponentInitial.GroupCentralQuotient

public section

namespace CFSG.StandardType

theorem eq_of_le_of_card_centralQuotient_le {G : Type*} [Group G] [Finite G] {H G₀ : Subgroup G}
    (hle : H ≤ G₀) (hperf : commutator ↥G₀ = ⊤)
    (hcard : Nat.card (↥G₀ ⧸ Subgroup.center ↥G₀) ≤ Nat.card (↥H ⧸ Subgroup.center ↥H)) :
    H = G₀ := by
  by_contra hne
  have hlt : H < G₀ := lt_of_le_of_ne hle hne
  haveI : Group.IsPerfect ↥G₀ := ⟨hperf⟩
  have h := CFSG.LocalAnalysis.ComponentInitial.index_center_lt_of_lt hlt
  rw [Subgroup.index_eq_card, Subgroup.index_eq_card] at h
  exact absurd h (not_lt.mpr hcard)

end CFSG.StandardType

end
