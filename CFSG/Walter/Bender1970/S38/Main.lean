module

public import CFSG.Walter.Bender1970.S38.JR
public import CFSG.Walter.Bender1970.S38.Induced

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter

variable {G : Type} [Group G] [Finite G]

theorem bender1970_3_8
    (hG : BenderCounterexample G) {t : G} (ht : orderOf t = 2)
    {H : Subgroup G} (hH : H ∈ benderM t) (T : Sylow 2 G) (htT : t ∈ (T : Subgroup G))
    {K : Subgroup G} (hK : IsComponentOf K H)
    (hFstar : ∀ s : G, orderOf s = 2 → ∀ M ∈ benderM s, s ∈ generalizedFittingSubgroupOf M)
    (hM : ∀ s ∈ (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G), orderOf s = 2 →
      benderM s = {H}) :
    Subgroup.normalizer ((T : Subgroup G) : Set G) ≤ H := by
  by_contra hN
  obtain ⟨hW2, hQ4⟩ := hG.card_eq_two_and_four ht hH T htT hK hM hN
  exact hG.false_of_card_eq_two ht hH T htT hK hFstar hM hN hW2 hQ4

theorem bender1970_3_8_of_isComponentOf_layer
    (hG : BenderCounterexample G) {t : G}
    (ht : orderOf t = 2) {H : Subgroup G} (hH : H ∈ benderM t) (T : Sylow 2 G)
    (htT : t ∈ (T : Subgroup G)) {K : Subgroup G} (hK : IsComponentOf K (componentLayerOf H))
    (hFstar : ∀ s : G, orderOf s = 2 → ∀ M ∈ benderM s, s ∈ generalizedFittingSubgroupOf M)
    (hM : ∀ s ∈ (T : Subgroup G) ⊓ Subgroup.centralizer (K : Set G), orderOf s = 2 →
      benderM s = {H}) :
    Subgroup.normalizer ((T : Subgroup G) : Set G) ≤ H :=
  bender1970_3_8 hG ht hH T htT (isComponentOf_of_isSubnormal (componentLayerOf_isNormalIn H).1
    (isSubnormal_subgroupOf_of_isNormalIn (componentLayerOf_isNormalIn H)) hK) hFstar hM

end CFSG.Walter
