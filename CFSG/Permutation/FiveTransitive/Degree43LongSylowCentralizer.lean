module

public import CFSG.Permutation.FiveTransitive.Degree28ThirteenCentralizer

public section

namespace CFSG

namespace FiveTransitive.Degree43LongSylowCentralizer
open MulAction

theorem centralizer_card_dvd
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 43)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    {p : ℕ} (hp : p = 41 ∨ p = 43)
    (S : Sylow p P) (hScard : Nat.card S = p) :
    Nat.card (Subgroup.centralizer (S : Set P)) ∣ p := by
  classical
  have hpprime : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  let _ : Fact p.Prime := ⟨hpprime⟩
  let _ : IsCyclic S := isCyclic_of_prime_card hScard
  obtain ⟨u, huRaw⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have huorder : orderOf u = p := huRaw.trans hScard
  let uP : P := u
  let g : Equiv.Perm X := uP
  have huPorder : orderOf uP = p := (Subgroup.orderOf_coe u).trans huorder
  have hgorder : orderOf g = p := (Subgroup.orderOf_coe uP).trans huPorder
  have hgcycle : g.IsCycle := Equiv.Perm.isCycle_of_prime_order'
    (by rwa [hgorder]) (by rw [hcard,hgorder]; rcases hp with rfl | rfl <;> omega)
  have hcycleType : g.cycleType = {p} := by rw [hgcycle.cycleType, ← hgcycle.orderOf, hgorder]
  have hgsupport : g.support.card = p := by rw [← hgcycle.orderOf,hgorder]
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
        wPerm.support.card ≤ 2 := by
      calc
        wPerm.support.card ≤ g.supportᶜ.card :=
          Finset.card_le_card hwSupportSubset
        _ ≤ 2 := by
          rw [Finset.card_compl, hcard, hgsupport]
          rcases hp with rfl | rfl <;> norm_num
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
      Fintype.card g.support = p := by
    rw [Fintype.card_coe, hgsupport]
  have hsupportCentralizerCard :
      Nat.card
          (Subgroup.centralizer
            ({gSupport} :
              Set (Equiv.Perm g.support))) = p := by
    rw [Equiv.Perm.nat_card_centralizer,
      hgSupportCycleType, hcycleType,
      hsupportTypeCard]
    rcases hp with rfl | rfl <;> norm_num
  have hCdvdSupport : Nat.card C ∣ p := by
    rw [← hsupportCentralizerCard]
    exact Subgroup.card_dvd_of_injective
      supportCentMap hsupportCentMapInjective
  exact hCdvdSupport

theorem fortyone_fixed_card
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 43)
    (S : Sylow 41 P) (hS : Nat.card S = 41) : Nat.card (MulAction.fixedPoints S X) = 2 := by
  classical
  let _ : Fact (Nat.Prime 41) := ⟨by norm_num⟩
  let _ : IsCyclic S := isCyclic_of_prime_card hS
  obtain ⟨u,hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have hgorder : orderOf u.val.val = 41 := by
    rw [Subgroup.orderOf_coe,Subgroup.orderOf_coe]
    exact hu.trans hS
  have hcycle : u.val.val.IsCycle := Equiv.Perm.isCycle_of_prime_order'
    (by rw [hgorder]; norm_num) (by rw [hgorder,hcard]; omega)
  have hsupport : u.val.val.support.card = 41 := by rw [← hcycle.orderOf,hgorder]
  have hsub : MulAction.fixedPoints S X ⊆ Function.fixedPoints u.val.val := by
    intro x hx
    exact MulAction.mem_fixedPoints.mp hx u
  have hle := Set.ncard_le_ncard hsub
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    Nat.card_eq_fintype_card (α := Function.fixedPoints u.val.val),
    Equiv.Perm.card_fixedPoints,u.val.val.sum_cycleType,hcard,hsupport] at hle
  change Nat.card (MulAction.fixedPoints S X) ≤ 2 at hle
  have hm := S.isPGroup'.card_modEq_card_fixedPoints X
  change Nat.card X % 41 = Nat.card (MulAction.fixedPoints S X) % 41 at hm
  rw [Nat.card_eq_fintype_card,hcard] at hm
  omega

end FiveTransitive.Degree43LongSylowCentralizer

end CFSG
