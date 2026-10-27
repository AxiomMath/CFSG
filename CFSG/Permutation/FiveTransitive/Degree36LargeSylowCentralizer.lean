module

public import CFSG.Permutation.FiveTransitive.Degree36LargeSylowEntrance
import CFSG.Permutation.FiveTransitive.Degree48LargeSylowCentralizer
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric

public section

namespace CFSG

namespace FiveTransitive.Degree36LargeSylowCentralizer

open MulAction

private theorem centralizer_card_dvd_power
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    {p : ℕ} (hp : p = 17 ∨ p = 11) (S : Sylow p P) :
    Nat.card (Subgroup.centralizer (S : Set P)) ∣ (36 / p).factorial * p ^ (36 / p) := by
  classical
  let _ : Fact p.Prime := ⟨by rcases hp with rfl | rfl <;> norm_num⟩
  have hScard := Degree36LargeSylowEntrance.sylow_card P hcard h5 hnotAlt hp S
  let _ : IsCyclic S := isCyclic_of_prime_card hScard
  obtain ⟨u, huRaw⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have huorder : orderOf u = p := huRaw.trans hScard
  let uP : P := u
  let g : Equiv.Perm X := uP
  have huPorder : orderOf uP = p := (Subgroup.orderOf_coe u).trans huorder
  have hcycleType : g.cycleType = Multiset.replicate (36 / p) p :=
    Degree36LargeSylowEntrance.element_cycle_type P hcard h5 hnotAlt hp uP huPorder
  have hgsupport : g.support.card = (36 / p) * p := by
    rw [← g.sum_cycleType,hcycleType,Multiset.sum_replicate,nsmul_eq_mul,Nat.cast_id]
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
        wPerm.support.card ≤ 3 := by
      calc
        wPerm.support.card ≤ g.supportᶜ.card :=
          Finset.card_le_card hwSupportSubset
        _ ≤ 3 := by
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
      Fintype.card g.support = (36 / p) * p := by
    rw [Fintype.card_coe, hgsupport]
  have hsupportCentralizerCard :
      Nat.card
          (Subgroup.centralizer
            ({gSupport} :
              Set (Equiv.Perm g.support))) = (36 / p).factorial * p ^ (36 / p) := by
    rw [Equiv.Perm.nat_card_centralizer,
      hgSupportCycleType, hcycleType,
      hsupportTypeCard]
    rcases hp with rfl | rfl <;> norm_num
  have hCdvdSupport : Nat.card C ∣ (36 / p).factorial * p ^ (36 / p) := by
    rw [← hsupportCentralizerCard]
    exact Subgroup.card_dvd_of_injective
      supportCentMap hsupportCentMapInjective
  exact hCdvdSupport

theorem centralizer_card_dvd
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    {p : ℕ} (hp : p = 17 ∨ p = 11) (S : Sylow p P) :
    Nat.card (Subgroup.centralizer (S : Set P)) ∣ p * (36 / p).factorial := by
  have hprime : p.Prime := by rcases hp with rfl | rfl <;> norm_num
  have hbound := ((Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
    (Subgroup.card_subgroup_dvd_card (Subgroup.centralizer (S : Set P)))) p
  rw [Degree36LargeSylowEntrance.factorization_eq_one P hcard h5 hnotAlt hp] at hbound
  apply FiveTransitive.Degree48LargeSylowCentralizer.remove_prime_powers hprime Nat.card_pos.ne' (Nat.factorial_ne_zero _)
  · rw [mul_comm]
    exact centralizer_card_dvd_power P hcard h5 hnotAlt hp S
  · exact hbound

end FiveTransitive.Degree36LargeSylowCentralizer

end CFSG
