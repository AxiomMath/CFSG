module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27Infra
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_16

namespace CFSG
end CFSG
open CFSG

/-!
# A centralized involution forces a nontrivial two-core

When the component layer is trivial, the generalized Fitting subgroup is the
ordinary Fitting subgroup.  Its self-centralizing property then makes any
involution centralizing the Fitting subgroup lie in it.  The two/odd
decomposition of the Fitting subgroup forces such an involution into the
two-core.
-/

namespace CFSG.GorensteinWalter

universe u

/-- If `E(G)=1` and an involution centralizes `F(G)`, then `O₂(G)` is
nontrivial. -/
public theorem twoCoreOf_ne_bot_of_involution_centralizes_fitting_of_componentLayer_eq_bot
    {G : Type u} [Group G] [Finite G]
    (B : Subgroup G) (t : G) (htB : t ∈ B) (ht : IsInvolution t)
    (hE : componentLayerOf B = ⊥)
    (htF : t ∈ Subgroup.centralizer (fittingSubgroupOf B : Set G)) :
    twoCoreOf B ≠ ⊥ := by
  have hFstar : generalizedFittingSubgroupOf B = fittingSubgroupOf B := by
    simp [generalizedFittingSubgroupOf, hE]
  have htFstarCent :
      t ∈ Subgroup.centralizer
        (generalizedFittingSubgroupOf B : Set G) := by
    simpa [hFstar] using htF
  have htFit : t ∈ fittingSubgroupOf B := by
    have htFstar := centralizer_intersection_fstar_le_fstar B ⟨htFstarCent, htB⟩
    simpa [hFstar] using htFstar
  intro hO2
  have hpcore : pCore 2 B = ⊥ := by
    exact (Subgroup.map_eq_bot_iff_of_injective (pCore 2 B) (f := B.subtype)
      B.subtype_injective).1 (by simpa [twoCoreOf] using hO2)
  have hFitInternal : fittingSubgroup B ≤ pPrimeCore 2 B := by
    have hle := fittingSubgroup_le_sup_pCore_pPrimeCore (G := B)
    simpa [hpcore] using hle
  have hFitOdd : fittingSubgroupOf B ≤ oddCoreOf B := by
    have hmap := Subgroup.map_mono (f := B.subtype) hFitInternal
    simpa [fittingSubgroupOf, oddCoreOf] using hmap
  have htOdd : t ∈ oddCoreOf B := hFitOdd htFit
  have hord : orderOf t = 2 := orderOf_eq_prime ht.2 ht.1
  rcases Subgroup.mem_map.mp htOdd with ⟨u, hu, hut⟩
  have hordU : orderOf u = 2 := by
    calc
      orderOf u = orderOf (B.subtype u) :=
        (orderOf_injective B.subtype B.subtype_injective u).symm
      _ = orderOf t := congrArg orderOf hut
      _ = 2 := hord
  have hdvd : orderOf u ∣ Nat.card (pPrimeCore 2 B) :=
    Subgroup.orderOf_dvd_natCard (pPrimeCore 2 B) hu
  have htwo : 2 ∣ Nat.card (pPrimeCore 2 B) := by
    simpa [hordU] using hdvd
  exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp
    (pPrimeCore_coprime_card (G := B) (p := 2))) htwo

end CFSG.GorensteinWalter
