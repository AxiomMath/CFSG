module

public import CFSG.Permutation.FiveTransitive.Degree19DoubleFiveCentralizer
public import CFSG.Permutation.FiveTransitive.Degree24Order567

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

theorem sylowSeven_centralizer_card_dvd_ninety_eight
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 7 (fixingSubgroup P s))
    (hScard : Nat.card S = 7) :
    Nat.card
        (Subgroup.centralizer
          (S : Set (fixingSubgroup P s))) ∣
      98 := by
  classical
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let H : Subgroup P := fixingSubgroup P s
  letI : IsCyclic S :=
    isCyclic_of_prime_card hScard
  obtain ⟨u, huOrderRaw⟩ :=
    IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have huOrderS : orderOf u = 7 :=
    huOrderRaw.trans hScard
  let uH : H := u
  let uP : P := uH
  let g : Equiv.Perm X := uP
  have huOrderH : orderOf uH = 7 := by
    calc
      orderOf uH = orderOf u :=
        Subgroup.orderOf_coe _
      _ = 7 := huOrderS
  have hgOrder : orderOf g = 7 := by
    calc
      orderOf g = orderOf uP :=
        Subgroup.orderOf_coe _
      _ = orderOf uH :=
        Subgroup.orderOf_coe _
      _ = 7 := huOrderH
  have hgSupport : g.support.card = 14 :=
    order_seven_mem_five_stabilizer_support_eq_fourteen
      X P hcard h5 hnotAlt s hs uH huOrderH
  have hgPrime : (orderOf g).Prime := by
    rw [hgOrder]
    norm_num
  obtain ⟨k, hk⟩ :=
    Equiv.Perm.cycleType_prime_order hgPrime
  have hsum := g.sum_cycleType
  rw [hk, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, hgOrder, hgSupport] at hsum
  have hkTwo : k + 1 = 2 := by omega
  have hgCycleType : g.cycleType = {7, 7} := by
    rw [hk, hgOrder, hkTwo]
    norm_num
  let C : Subgroup H :=
    Subgroup.centralizer (S : Set H)
  let baseMap : C →* Equiv.Perm X :=
    P.subtype.comp (H.subtype.comp C.subtype)
  have hbaseMapInjective : Function.Injective baseMap := by
    intro a b hab
    exact
      C.subtype_injective
        (H.subtype_injective
          (P.subtype_injective hab))
  have hbaseMapMem :
      ∀ q : C, baseMap q ∈
        Subgroup.centralizer
          ({g} : Set (Equiv.Perm X)) := by
    intro q
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hqCommuteH : Commute (q.1 : H) uH :=
      (q.prop uH u.prop).symm
    exact
      congrArg Subtype.val
        (congrArg Subtype.val hqCommuteH)
  let centMap :
      C →*
        Subgroup.centralizer
          ({g} : Set (Equiv.Perm X)) :=
    baseMap.codRestrict
      (Subgroup.centralizer
        ({g} : Set (Equiv.Perm X)))
      hbaseMapMem
  let supportMap : C →* Equiv.Perm g.support :=
    (Degree19.centralizerToSupport g).comp centMap
  let gSupport : Equiv.Perm g.support :=
    g.subtypePerm (fun _ => g.apply_mem_support)
  have hsupportMapMem :
      ∀ q : C, supportMap q ∈
        Subgroup.centralizer
          ({gSupport} :
            Set (Equiv.Perm g.support)) := by
    intro q
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change baseMap q (g x.1) =
      g (baseMap q x.1)
    have hcomm : Commute (baseMap q) g :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (centMap q).prop
    exact
      congrFun
        (congrArg DFunLike.coe hcomm.eq) x.1
  let supportCentMap :
      C →*
        Subgroup.centralizer
          ({gSupport} :
            Set (Equiv.Perm g.support)) :=
    supportMap.codRestrict
      (Subgroup.centralizer
        ({gSupport} :
          Set (Equiv.Perm g.support)))
      hsupportMapMem
  have hgSupportExtend :
      Equiv.Perm.ofSubtype gSupport = g := by
    exact Equiv.Perm.ofSubtype_subtypePerm
      (fun _ => g.apply_mem_support)
      (fun x hx => Equiv.Perm.mem_support.mpr hx)
  have hgSupportCycleType :
      gSupport.cycleType = g.cycleType := by
    rw [← Equiv.Perm.cycleType_ofSubtype,
      hgSupportExtend]
  have hsupportCentralizerCard :
      Nat.card
          (Subgroup.centralizer
            ({gSupport} :
              Set (Equiv.Perm g.support))) = 98 := by
    have hsupportSubtypeCard :
        Fintype.card g.support = 14 := by
      calc
        Fintype.card g.support = g.support.card :=
          Fintype.card_coe _
        _ = 14 := hgSupport
    rw [Equiv.Perm.nat_card_centralizer,
      hgSupportCycleType, hgCycleType,
      hsupportSubtypeCard]
    norm_num
  have hsupportCentMapInjective :
      Function.Injective supportCentMap := by
    intro a b hab
    by_contra habNe
    let w : C := a * b⁻¹
    have hwNe : w ≠ 1 := by
      intro hw
      exact habNe (mul_inv_eq_one.mp hw)
    have hwSupportCentOne :
        supportCentMap w = 1 := by
      dsimp only [w]
      rw [map_mul, map_inv, hab]
      exact mul_inv_cancel _
    have hwSupportOne :
        supportMap w = 1 :=
      congrArg Subtype.val hwSupportCentOne
    let wH : H := w
    let wP : P := wH
    let wPerm : Equiv.Perm X := wP
    have hwFixSupport :
        ∀ x ∈ g.support, wPerm x = x := by
      intro x hx
      have happly :=
        congrFun
          (congrArg DFunLike.coe hwSupportOne)
          (⟨x, hx⟩ : g.support)
      exact congrArg Subtype.val happly
    have hwFixS :
        ∀ x ∈ s, wPerm x = x := by
      exact (mem_fixingSubgroup_iff P).mp wH.prop
    have hSupportDisjoint :
        Disjoint (g.support : Set X) s := by
      rw [Set.disjoint_left]
      intro x hxg hxs
      exact
        Equiv.Perm.mem_support.mp hxg
          ((mem_fixingSubgroup_iff P).mp
            uH.prop x hxs)
    let U : Set X := (g.support : Set X) ∪ s
    have hUncard : U.ncard = 19 := by
      change ((g.support : Set X) ∪ s).ncard = 19
      rw [Set.ncard_union_eq hSupportDisjoint,
        Set.ncard_coe_finset, hgSupport, hs]
    have hUcomplCard : Uᶜ.ncard = 5 := by
      have htotal := Set.ncard_add_ncard_compl U
      rw [Nat.card_eq_fintype_card, hcard,
        hUncard] at htotal
      omega
    have hwSupportSubset :
        (wPerm.support : Set X) ⊆ Uᶜ := by
      intro x hx
      rw [Set.mem_compl_iff]
      intro hxU
      apply Equiv.Perm.mem_support.mp hx
      rcases hxU with hxg | hxs
      · exact hwFixSupport x hxg
      · exact hwFixS x hxs
    have hwSupportCard :
        wPerm.support.card ≤ 5 := by
      rw [← Set.ncard_coe_finset]
      exact
        (Set.ncard_le_ncard hwSupportSubset).trans_eq
          hUcomplCard
    have hwPermNe : wPerm ≠ 1 := by
      intro hwOne
      apply hwNe
      apply hbaseMapInjective
      rw [map_one]
      exact hwOne
    exact hnotAlt
      (alternatingGroup_le_of_nontrivial_support_le_seven
        X P hcard h5 wP.prop hwPermNe (by
          change wPerm.support.card ≤ 7
          omega))
  rw [← hsupportCentralizerCard]
  exact
    Subgroup.card_dvd_of_injective
      supportCentMap hsupportCentMapInjective

end FiveTransitive.Degree24

end CFSG
