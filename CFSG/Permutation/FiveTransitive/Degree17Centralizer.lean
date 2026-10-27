module

public import CFSG.Permutation.FiveTransitive.Helpers
public import CFSG.Permutation.FiveTransitive.PermCentralizer

public section

namespace CFSG

namespace FiveTransitive.Degree17

open MulAction SubMulAction Subgroup

theorem centralizer_card_eq_thirteen_of_not_alternating
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 17)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (u : P) (huorder : orderOf u = 13) :
    Nat.card (Subgroup.centralizer ({u} : Set P)) = 13 := by
  classical
  let g : Equiv.Perm X := u
  have hgorder : orderOf g = 13 := by
    calc
      orderOf g = orderOf u := Subgroup.orderOf_coe _
      _ = 13 := huorder
  have hgcycle : g.IsCycle :=
    Equiv.Perm.isCycle_of_prime_order' (by
      rw [hgorder]
      norm_num) (by
        rw [hcard, hgorder]
        norm_num)
  have hgsupport : g.support.card = 13 := by
    rw [← hgcycle.orderOf, hgorder]
  have hcentralizerPerm :
      Nat.card (Subgroup.centralizer
        ({g} : Set (Equiv.Perm X))) = 312 := by
    rw [Equiv.Perm.nat_card_centralizer, hgcycle.cycleType,
      hgsupport, hcard]
    norm_num
  let C : Subgroup P :=
    Subgroup.centralizer ({u} : Set P)
  let baseMap : C →* Equiv.Perm X :=
    P.subtype.comp C.subtype
  have hbaseMapMem :
      ∀ c : C, baseMap c ∈
        Subgroup.centralizer ({g} : Set (Equiv.Perm X)) := by
    intro c
    change ((c.1 : P) : Equiv.Perm X) ∈
      Subgroup.centralizer ({g} : Set (Equiv.Perm X))
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_singleton_iff.mp c.prop)
  let centMap :
      C →* Subgroup.centralizer ({g} : Set (Equiv.Perm X)) :=
    baseMap.codRestrict
      (Subgroup.centralizer ({g} : Set (Equiv.Perm X)))
      hbaseMapMem
  have hcentMapInjective : Function.Injective centMap := by
    intro a b hab
    have hab' := congrArg Subtype.val hab
    change baseMap a = baseMap b at hab'
    exact C.subtype_injective (P.subtype_injective hab')
  have hCdiv : Nat.card C ∣ 312 := by
    rw [← hcentralizerPerm]
    exact Subgroup.card_dvd_of_injective
      centMap hcentMapInjective
  have huC : u ∈ C := by
    rw [Subgroup.mem_centralizer_singleton_iff]
  have hZC : Subgroup.zpowers u ≤ C :=
    Subgroup.zpowers_le.mpr huC
  have h13divC : 13 ∣ Nat.card C := by
    rw [← huorder, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le hZC
  have himpossible {q : ℕ} (hq : q.Prime)
      (hqcop : Nat.Coprime q 13)
      (hqdvd : q ∣ Nat.card C) : False := by
    letI : Fact q.Prime := ⟨hq⟩
    obtain ⟨v, hv⟩ :=
      exists_prime_orderOf_dvd_card' q hqdvd
    let w : Equiv.Perm X := (v : P)
    have hworder : orderOf w = q := by
      calc
        orderOf w = orderOf (v : P) := Subgroup.orderOf_coe _
        _ = orderOf v := Subgroup.orderOf_coe _
        _ = q := hv
    have hcomm : Commute w g :=
      congrArg Subtype.val
        (Subgroup.mem_centralizer_singleton_iff.mp v.prop)
    have hcoprime :
        Nat.Coprime (orderOf w) (orderOf g) := by
      rw [hworder, hgorder]
      exact hqcop
    have hsuppSubset :=
      PermCentralizer.support_le_compl_of_isCycle_of_commute_of_coprime_order
        hgcycle hcomm hcoprime
    have hsuppCard : w.support.card ≤ 5 := by
      calc
        w.support.card ≤ g.supportᶜ.card :=
          Finset.card_le_card hsuppSubset
        _ = 17 - 13 := by
          rw [Finset.card_compl, hgsupport, hcard]
        _ ≤ 5 := by norm_num
    have hwNe : w ≠ 1 := by
      intro hw
      rw [hw, orderOf_one] at hworder
      exact hq.ne_one hworder.symm
    exact hnotAlt
      (Helpers.alternatingGroup_le_of_nontrivial_card_support_le_five
        X P h5 (by omega) (v : P).prop hwNe (by
          simpa only [w] using hsuppCard))
  have hnotTwo : ¬2 ∣ Nat.card C := by
    exact himpossible (q := 2) (by norm_num) (by norm_num)
  have hnotThree : ¬3 ∣ Nat.card C := by
    exact himpossible (q := 3) (by norm_num) (by norm_num)
  have hcoprimeEight : Nat.Coprime (Nat.card C) (2 ^ 3) :=
    Nat.prime_two.coprime_pow_of_not_dvd hnotTwo
  have hcoprimeThree : Nat.Coprime (Nat.card C) 3 :=
    (Nat.prime_three.coprime_iff_not_dvd.mpr hnotThree).symm
  have hcoprimeTwentyFour : Nat.Coprime (Nat.card C) 24 := by
    rw [show 24 = 3 * 2 ^ 3 by norm_num]
    exact hcoprimeThree.mul_right hcoprimeEight
  have hCdvdThirteen : Nat.card C ∣ 13 := by
    apply hcoprimeTwentyFour.dvd_of_dvd_mul_left
    norm_num at hCdiv ⊢
    exact hCdiv
  exact Nat.dvd_antisymm hCdvdThirteen h13divC

end FiveTransitive.Degree17

end CFSG
