module

public import CFSG.Walter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_17iii
import CFSG.Walter.Bender1970.S1.EqualityOfMaximalFitting
import CFSG.Walter.Bender1970.S1.EqualityOfMaximalLayer
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ComponentLayerConjugate
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ComponentLayerPerfect
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FittingSubgroupConjugate

public section

namespace CFSG.Walter

open GorensteinWalter

universe u

theorem bender1970_1_7_iv_equalityOfMaximal
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (A : Subgroup G) (hA : IsCoatom A)
    (S : Subgroup G)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S)
    {B : Subgroup G} (hSB : S ≤ B) (hB : IsCoatom B)
    (hpi : 2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf A)) ∨
      2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf B)))
    (hBstar : IsAStar ↥B)
    (hE : Nat.card (componentLayerOf B) ≤ Nat.card (componentLayerOf A))
    (hO : ∀ q : ℕ, q.Prime → q ∉ primesOfOrder (_root_.CFSG.fittingSubgroupOf A) →
      qCoreOf B q = ⊥) :
    A = B := by
  have hFBA : _root_.CFSG.fittingSubgroupOf B ≤ A :=
    fittingSubgroupOf_le_of_pResidualOf_ne_bot hsimple A hA S hSF hSsub hCS hSB
      (fun _p hp _ => pResidualOf_generalizedFittingSubgroupOf_ne_bot A B hpi hE hO hp) hO
  have hFBE : _root_.CFSG.fittingSubgroupOf B ≤
      Subgroup.centralizer (componentLayerOf A : Set G) :=
    fittingSubgroupOf_le_centralizer_componentLayerOf hsimple A hA S hSF hSsub hCS hSB hO
  have hEAB : componentLayerOf A ≤ B :=
    (fstar_componentLayer_le_selfCentralizingSubnormal A S hSF hSsub hCS).trans hSB
  have hEeq : componentLayerOf A = componentLayerOf B :=
    Subgroup.eq_of_le_of_card_ge (le_componentLayerOf_of_isAStar hBstar hEAB
      (componentLayerOf_isPerfect A) (Subgroup.le_centralizer_iff.mp hFBE)) hE
  have hFstarBA : generalizedFittingSubgroupOf B ≤ A :=
    sup_le hFBA (hEeq ▸ (le_sup_right.trans (generalizedFittingSubgroupOf_le A)))
  refine bender1970_1_7_iii_equalityOfMaximal hsimple A hA S hSF hSsub hCS hSB hB hpi
    ⟨generalizedFittingSubgroupOf B, hFstarBA, le_rfl, ?_, inf_le_left⟩
  rw [Subgroup.subgroupOf_self]
  exact Subgroup.IsSubnormal.top

theorem bender1970_1_7_v_equalityOfMaximal
    {G : Type u} [Group G] [Finite G]
    (hsimple : IsSimpleGroup G)
    (A : Subgroup G) (hA : IsCoatom A)
    (S : Subgroup G)
    (hSF : S ≤ generalizedFittingSubgroupOf A)
    (hSsub : (S.subgroupOf (generalizedFittingSubgroupOf A)).IsSubnormal)
    (hCS : generalizedFittingSubgroupOf A ⊓ Subgroup.centralizer (S : Set G) ≤ S)
    {B : Subgroup G} (hSB : S ≤ B) (hB : IsCoatom B)
    (hpi : 2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf A)) ∨
      2 ≤ Nat.card (primesOfOrder (generalizedFittingSubgroupOf B)))
    (hBstar : IsAStar ↥B) (hconj : ∃ g : G, B = A.map (MulAut.conj g).toMonoidHom) :
    A = B := by
  obtain ⟨g, hg⟩ := hconj
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  refine bender1970_1_7_iv_equalityOfMaximal hsimple A hA S hSF hSsub hCS hSB hB hpi hBstar ?_ ?_
  · have hEB : componentLayerOf B = (componentLayerOf A).map (MulAut.conj g).toMonoidHom := by
      rw [hg]
      exact componentLayerOf_conjugateSubgroup A g
    rw [hEB, Subgroup.card_map_of_injective hinj]
  · intro q hq hqA
    by_contra hne
    have hFB : _root_.CFSG.fittingSubgroupOf B =
        (_root_.CFSG.fittingSubgroupOf A).map (MulAut.conj g).toMonoidHom := by
      rw [hg]
      exact fittingSubgroupOf_conjugateSubgroup A g
    have hqB := mem_primesOfOrder_of_qCoreOf_ne_bot B q hq hne
    rw [show CFSG.GorensteinWalter.fittingSubgroupOf B = _ from hFB] at hqB
    change q ∈ (Nat.card _).primeFactors at hqB
    rw [Subgroup.card_map_of_injective hinj] at hqB
    exact hqA hqB

end CFSG.Walter
