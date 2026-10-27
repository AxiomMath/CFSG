module

public import CFSG.Permutation.FiveTransitive.HighDegreeManningSupport


public section

namespace CFSG

namespace FiveTransitive.Degree28ThirteenCentralizer

open MulAction

@[expose] def centralizerToSupport
    {X : Type} [Fintype X] [DecidableEq X]
    (g : Equiv.Perm X) :
    Subgroup.centralizer ({g} : Set (Equiv.Perm X)) →*
      Equiv.Perm g.support where
  toFun p :=
    p.1.subtypePerm
      (fun x =>
        Equiv.Perm.mem_support_iff_of_commute
          (Subgroup.mem_centralizer_singleton_iff.mp p.2) x)
  map_one' := by
    ext x
    rfl
  map_mul' a b := by
    ext x
    rfl

theorem order_thirteen_cycle_type
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 28)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (u : P) (huorder : orderOf u = 13) :
    (u : Equiv.Perm X).cycleType = {13, 13} := by
  classical
  let g : Equiv.Perm X := u
  have hgorder : orderOf g = 13 := (Subgroup.orderOf_coe u).trans huorder
  have hgprime : (orderOf g).Prime := by rw [hgorder]; norm_num
  obtain ⟨k, hk⟩ := Equiv.Perm.cycleType_prime_order hgprime
  have hsum := g.sum_cycleType
  rw [hk, Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id, hgorder] at hsum
  have hle : g.support.card ≤ 28 := hcard ▸ Finset.card_le_univ g.support
  have hne : g ≠ 1 := by intro h; simp [h] at hgorder
  have hmin := HighDegreeManningSupport.degree_le_two_mul_support
    P (by omega) h5 hnotAlt u.prop hne
  rw [hcard] at hmin
  have hkTwo : k + 1 = 2 := by change 28 ≤ 2 * g.support.card at hmin; omega
  change g.cycleType = _
  rw [hk, hgorder, hkTwo]
  norm_num

theorem centralizer_card_dvd
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 28)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (S : Sylow 13 P) (hScard : Nat.card S = 13) :
    Nat.card (Subgroup.centralizer (S : Set P)) ∣ 338 := by
  classical
  let _ : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  let _ : IsCyclic S := isCyclic_of_prime_card hScard
  obtain ⟨u, huRaw⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have huorder : orderOf u = 13 := huRaw.trans hScard
  let uP : P := u
  let g : Equiv.Perm X := uP
  have huPorder : orderOf uP = 13 := (Subgroup.orderOf_coe u).trans huorder
  have hcycleType : g.cycleType = {13,13} :=
    order_thirteen_cycle_type P hcard h5 hnotAlt uP huPorder
  have hgsupport : g.support.card = 26 := by
    rw [← g.sum_cycleType, hcycleType]
    norm_num
  let C : Subgroup P :=
    Subgroup.centralizer (S : Set P)
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
    (centralizerToSupport g).comp centMap
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
        wPerm.support.card ≤ 2 := by
      calc
        wPerm.support.card ≤ g.supportᶜ.card :=
          Finset.card_le_card hwSupportSubset
        _ = 2 := by
          rw [Finset.card_compl, hcard, hgsupport]
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
  have hsupportTypeCard :
      Fintype.card g.support = 26 := by
    rw [Fintype.card_coe, hgsupport]
  have hsupportCentralizerCard :
      Nat.card
          (Subgroup.centralizer
            ({gSupport} :
              Set (Equiv.Perm g.support))) = 338 := by
    rw [Equiv.Perm.nat_card_centralizer,
      hgSupportCycleType, hcycleType,
      hsupportTypeCard]
    norm_num
  have hCdvdSupport : Nat.card C ∣ 338 := by
    rw [← hsupportCentralizerCard]
    exact Subgroup.card_dvd_of_injective
      supportCentMap hsupportCentMapInjective
  exact hCdvdSupport

end FiveTransitive.Degree28ThirteenCentralizer

end CFSG
