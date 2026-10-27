module

public import CFSG.Permutation.FiveTransitive.Degree19DoubleFiveCentralizer
public import CFSG.Permutation.FiveTransitive.Degree25DoubleEleven

public section

namespace CFSG

namespace FiveTransitive.Degree25

open MulAction SubMulAction Subgroup

theorem local_sylow_eleven_centralizer_card_dvd_two_hundred_forty_two
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (e : Fin 3 ↪ X)
    (J : Subgroup P)
    (hJ : J = fixingSubgroup P (Set.range e))
    (T : Sylow 11 J) (hTcard : Nat.card T = 11) :
    Nat.card
        (Subgroup.centralizer ((T : Subgroup J) : Set J)) ∣
      242 := by
  classical
  letI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  letI : IsCyclic T := isCyclic_of_prime_card hTcard
  letI : IsMulCommutative T := IsCyclic.isMulCommutative
  obtain ⟨u, huorder⟩ :=
    IsCyclic.exists_ofOrder_eq_natCard (α := T)
  have huorderT : orderOf u = 11 := huorder.trans hTcard
  have huorderJ : orderOf (u : J) = 11 := by
    calc
      orderOf (u : J) = orderOf u := Subgroup.orderOf_coe _
      _ = 11 := huorderT
  have huorderP : orderOf ((u : J) : P) = 11 := by
    calc
      orderOf ((u : J) : P) = orderOf (u : J) :=
        Subgroup.orderOf_coe _
      _ = 11 := huorderJ
  let g : Equiv.Perm X := ((u : J) : P)
  have hcycleType : g.cycleType = {11, 11} := by
    simpa only [g] using
      order_eleven_cycleType_eq_double
        X P hcard h5 hnotAlt ((u : J) : P) huorderP
  have hgsupport : g.support.card = 22 := by
    have hsum := g.sum_cycleType
    rw [hcycleType] at hsum
    norm_num at hsum
    exact hsum.symm
  have hecard : (Set.range e).ncard = 3 := by
    rw [Set.ncard_range_of_injective e.injective,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hRangeSubset :
      Set.range e ⊆ (g.support : Set X)ᶜ := by
    intro x hx
    rw [Set.mem_compl_iff]
    intro hxSupport
    apply Equiv.Perm.mem_support.mp hxSupport
    have hJle :
        J ≤ fixingSubgroup P (Set.range e) :=
      le_of_eq hJ
    have huFix :
        ∀ y ∈ Set.range e,
          (((u : J) : P) : Equiv.Perm X) y = y := by
      exact
        (mem_fixingSubgroup_iff P).mp
          (hJle (u : J).prop)
    exact huFix x hx
  have hComplementCard :
      ((g.support : Set X)ᶜ).ncard = 3 := by
    have htotal :=
      Set.ncard_add_ncard_compl (g.support : Set X)
    rw [Set.ncard_coe_finset,
      Nat.card_eq_fintype_card, hcard, hgsupport] at htotal
    omega
  have hRangeEqComplement :
      Set.range e = (g.support : Set X)ᶜ := by
    apply Set.eq_of_subset_of_ncard_le hRangeSubset
    rw [hComplementCard, hecard]
  let C : Subgroup J :=
    Subgroup.centralizer ((T : Subgroup J) : Set J)
  let baseMap : C →* Equiv.Perm X :=
    P.subtype.comp (J.subtype.comp C.subtype)
  have hbaseMapMem :
      ∀ q : C, baseMap q ∈
        Subgroup.centralizer ({g} : Set (Equiv.Perm X)) := by
    intro q
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hqCommuteJ : Commute (q.1 : J) (u : J) :=
      (q.prop (u : J) u.prop).symm
    exact
      congrArg Subtype.val
        (congrArg Subtype.val hqCommuteJ)
  let centMap :
      C →*
        Subgroup.centralizer ({g} : Set (Equiv.Perm X)) :=
    baseMap.codRestrict
      (Subgroup.centralizer ({g} : Set (Equiv.Perm X)))
      hbaseMapMem
  let supportMap : C →* Equiv.Perm g.support :=
    (FiveTransitive.Degree19.centralizerToSupport g).comp centMap
  let gSupport : Equiv.Perm g.support :=
    g.subtypePerm (fun _ => g.apply_mem_support)
  have hgSupportExtend :
      Equiv.Perm.ofSubtype gSupport = g := by
    exact Equiv.Perm.ofSubtype_subtypePerm
      (fun _ => g.apply_mem_support)
      (fun x hx => Equiv.Perm.mem_support.mpr hx)
  have hgSupportCycleType :
      gSupport.cycleType = g.cycleType := by
    rw [← Equiv.Perm.cycleType_ofSubtype,
      hgSupportExtend]
  have hsupportMapMem :
      ∀ q : C, supportMap q ∈
        Subgroup.centralizer
          ({gSupport} : Set (Equiv.Perm g.support)) := by
    intro q
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change baseMap q (g x.1) = g (baseMap q x.1)
    have hcomm : Commute (baseMap q) g :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (centMap q).prop
    exact
      congrFun
        (congrArg DFunLike.coe hcomm.eq) x.1
  let supportCentMap :
      C →*
        Subgroup.centralizer
          ({gSupport} : Set (Equiv.Perm g.support)) :=
    supportMap.codRestrict
      (Subgroup.centralizer
        ({gSupport} : Set (Equiv.Perm g.support)))
      hsupportMapMem
  have hsupportCentMapInjective :
      Function.Injective supportCentMap := by
    intro a b hab
    by_contra habNe
    let w : C := a * b⁻¹
    have hwNe : w ≠ 1 := by
      intro hw
      exact habNe (mul_inv_eq_one.mp hw)
    have hwSupportCentOne : supportCentMap w = 1 := by
      dsimp only [w]
      rw [map_mul, map_inv, hab]
      exact mul_inv_cancel _
    have hwSupportOne : supportMap w = 1 :=
      congrArg Subtype.val hwSupportCentOne
    let wJ : J := w
    let wP : P := wJ
    let wPerm : Equiv.Perm X := wP
    have hwFixSupport :
        ∀ x ∈ g.support, wPerm x = x := by
      intro x hx
      have happly :=
        congrFun
          (congrArg DFunLike.coe hwSupportOne)
          (⟨x, hx⟩ : g.support)
      exact congrArg Subtype.val happly
    have hwFixRange :
        ∀ x ∈ Set.range e, wPerm x = x := by
      have hJle :
          J ≤ fixingSubgroup P (Set.range e) :=
        le_of_eq hJ
      have hwJmem : (wJ : P) ∈
          fixingSubgroup P (Set.range e) := by
        exact hJle wJ.prop
      exact (mem_fixingSubgroup_iff P).mp hwJmem
    have hwPermOne : wPerm = 1 := by
      apply Equiv.ext
      intro x
      by_cases hx : x ∈ g.support
      · exact hwFixSupport x hx
      · apply hwFixRange
        rw [hRangeEqComplement]
        exact hx
    apply hwNe
    apply C.subtype_injective
    apply J.subtype_injective
    apply P.subtype_injective
    exact hwPermOne
  have hsupportTypeCard :
      Fintype.card g.support = 22 := by
    rw [Fintype.card_coe, hgsupport]
  have hfullCard :
      Nat.card
          (Subgroup.centralizer
            ({gSupport} : Set (Equiv.Perm g.support))) =
        242 := by
    rw [Equiv.Perm.nat_card_centralizer,
      hgSupportCycleType, hcycleType,
      hsupportTypeCard]
    norm_num
  rw [← hfullCard]
  exact
    Subgroup.card_dvd_of_injective
      supportCentMap hsupportCentMapInjective

end FiveTransitive.Degree25

end CFSG
