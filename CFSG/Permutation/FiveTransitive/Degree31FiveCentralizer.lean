module

public import CFSG.Permutation.FiveTransitive.Degree28ThirteenCentralizer

public section

namespace CFSG

namespace FiveTransitive.Degree31FiveCentralizer

open MulAction

theorem nine_not_dvd_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 31)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hfixed : 5 ≤ Nat.card (fixedPoints Q X))
    (u : Q) (huorder : orderOf u = 5) :
    ¬ 9 ∣ Nat.card (Subgroup.centralizer (Q : Set P)) := by
  classical
  let g : Equiv.Perm X := u.val
  have hgorder : orderOf g = 5 := by
    rw [Subgroup.orderOf_coe u.val,Subgroup.orderOf_coe u,huorder]
  have hgprime : (orderOf g).Prime := by rw [hgorder]; norm_num
  obtain ⟨m,hm⟩ := Equiv.Perm.cycleType_prime_order hgprime
  have hsum := g.sum_cycleType
  rw [hm,Multiset.sum_replicate,nsmul_eq_mul,Nat.cast_id,hgorder] at hsum
  have hne : g ≠ 1 := by intro h; rw [h,orderOf_one] at hgorder; omega
  have hmin := HighDegreeManningSupport.degree_le_two_mul_support
    P (by omega) h5 hnotAlt u.val.property hne
  rw [hcard] at hmin
  change 31 ≤ 2 * g.support.card at hmin
  have hsub : fixedPoints Q X ⊆ Function.fixedPoints g := fun x hx => hx u
  have hfixle := Set.ncard_le_ncard hsub
  rw [← Nat.card_coe_set_eq,← Nat.card_coe_set_eq,
    Nat.card_eq_fintype_card (α := Function.fixedPoints g),Equiv.Perm.card_fixedPoints,
    g.sum_cycleType,hcard] at hfixle
  have hsle : g.support.card ≤ 31 := hcard ▸ Finset.card_le_univ g.support
  have hcases : m + 1 = 4 ∨ m + 1 = 5 := by omega
  have hgsupport : 20 ≤ g.support.card := by omega
  let C : Subgroup P :=
    Subgroup.centralizer (Q : Set P)
  let baseMap : C →* Equiv.Perm X :=
    P.subtype.comp C.subtype
  have hbaseMapInjective :
      Function.Injective baseMap := by
    intro a b hab
    exact C.subtype_injective
      (P.subtype_injective hab)
  have hbaseMapMem :
      ∀ q : C, baseMap q ∈
        Subgroup.centralizer
          ({g} : Set (Equiv.Perm X)) := by
    intro q
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val
      ((q.prop (u : P) u.prop).symm)
  let centMap :
      C →*
        Subgroup.centralizer
          ({g} : Set (Equiv.Perm X)) :=
    baseMap.codRestrict
      (Subgroup.centralizer
        ({g} : Set (Equiv.Perm X)))
      hbaseMapMem
  let supportMap : C →* Equiv.Perm g.support :=
    (Degree28ThirteenCentralizer.centralizerToSupport g).comp centMap
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
    let wP : P := w
    let wPerm : Equiv.Perm X := wP
    have hwFixSupport :
        ∀ x ∈ g.support, wPerm x = x := by
      intro x hx
      have happly :=
        congrFun
          (congrArg DFunLike.coe hwSupportOne)
          (⟨x, hx⟩ : g.support)
      exact congrArg Subtype.val happly
    have hwSupportSubset :
        wPerm.support ⊆ g.supportᶜ := by
      intro x hx
      rw [Finset.mem_compl]
      intro hxg
      exact
        Equiv.Perm.mem_support.mp hx
          (hwFixSupport x hxg)
    have hwSupportCard :
        wPerm.support.card ≤ 11 := by
      calc
        wPerm.support.card ≤ g.supportᶜ.card :=
          Finset.card_le_card hwSupportSubset
        _ ≤ 11 := by
          rw [Finset.card_compl, hcard]
          omega
    have hwPermNe : wPerm ≠ 1 := by
      intro hwOne
      apply hwNe
      apply hbaseMapInjective
      rw [map_one]
      exact hwOne
    have hm := HighDegreeManningSupport.degree_le_two_mul_support
      P (by omega) h5 hnotAlt wP.prop hwPermNe
    change Fintype.card X ≤ 2 * wPerm.support.card at hm
    rw [hcard] at hm
    omega
  have hgSupportExtend :
      Equiv.Perm.ofSubtype gSupport = g := by
    exact Equiv.Perm.ofSubtype_subtypePerm
      (fun _ => g.apply_mem_support)
      (fun x hx => Equiv.Perm.mem_support.mpr hx)
  have hgSupportCycleType :
      gSupport.cycleType = g.cycleType := by
    rw [← Equiv.Perm.cycleType_ofSubtype,
      hgSupportExtend]
  have hd := Subgroup.card_dvd_of_injective supportCentMap hsupportCentMapInjective
  have hcentnot : ¬ 9 ∣ Nat.card
      (Subgroup.centralizer ({gSupport} : Set (Equiv.Perm g.support))) := by
    rw [Equiv.Perm.nat_card_centralizer,hgSupportCycleType,hm,hgorder,
      Fintype.card_coe,← hsum]
    rcases hcases with h | h <;> rw [h] <;> norm_num
  exact fun h => hcentnot (h.trans hd)

end FiveTransitive.Degree31FiveCentralizer

end CFSG
