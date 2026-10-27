module

public import CFSG.Permutation.FiveTransitive.SmallSupportGeneric
public import CFSG.Permutation.FiveTransitive.PermCentralizer

public section

namespace CFSG

namespace FiveTransitive.FewFixedPrimeCycle

open MulAction SubMulAction Subgroup

theorem centralizer_card_eq_prime_of_not_alternating
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    {p f : ℕ} (hp : p.Prime) (hpSeven : 7 ≤ p) (hfSix : f ≤ 6)
    (hcard : Fintype.card X = p + f)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (u : P) (huorder : orderOf u = p) :
    Nat.card (Subgroup.centralizer ({u} : Set P)) = p := by
  classical
  let g : Equiv.Perm X := u
  have hgorder : orderOf g = p := by
    calc
      orderOf g = orderOf u := Subgroup.orderOf_coe _
      _ = p := huorder
  have hgcycle : g.IsCycle :=
    Equiv.Perm.isCycle_of_prime_order' (by
      rw [hgorder]
      exact hp) (by
        rw [hcard, hgorder]
        omega)
  have hgsupport : g.support.card = p := by
    rw [← hgcycle.orderOf, hgorder]
  have hcentralizerPerm :
      Nat.card (Subgroup.centralizer
        ({g} : Set (Equiv.Perm X))) = f.factorial * p := by
    rw [Equiv.Perm.nat_card_centralizer, hgcycle.cycleType,
      hgsupport, hcard]
    simp
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
  have hCdiv : Nat.card C ∣ f.factorial * p := by
    rw [← hcentralizerPerm]
    exact Subgroup.card_dvd_of_injective
      centMap hcentMapInjective
  have huC : u ∈ C := by
    rw [Subgroup.mem_centralizer_singleton_iff]
  have hZC : Subgroup.zpowers u ≤ C :=
    Subgroup.zpowers_le.mpr huC
  have hpdivC : p ∣ Nat.card C := by
    rw [← huorder, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le hZC
  have himpossible {q : ℕ} (hq : q.Prime)
      (hqcop : Nat.Coprime q p)
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
    have hsuppCardFixed : w.support.card ≤ f := by
      calc
        w.support.card ≤ g.supportᶜ.card :=
          Finset.card_le_card hsuppSubset
        _ = Fintype.card X - g.support.card := by
          rw [Finset.card_compl]
        _ = f := by
          rw [hcard, hgsupport]
          omega
    have hsuppCard : w.support.card ≤ 6 :=
      hsuppCardFixed.trans hfSix
    have hwNe : w ≠ 1 := by
      intro hw
      rw [hw, orderOf_one] at hworder
      exact hq.ne_one hworder.symm
    have hcardEight : 8 ≤ Fintype.card X := by
      have hwTwo : 2 ≤ w.support.card :=
        Equiv.Perm.two_le_card_support_of_ne_one hwNe
      rw [hcard]
      omega
    exact hnotAlt
      (SmallSupportGeneric.alternatingGroup_le_of_nontrivial_support_le_six
        P hcardEight h5 (v : P).prop hwNe (by
          simpa only [w] using hsuppCard))
  have hcoprimeSmallPrime (q : ℕ) (hq : q.Prime) (hqle : q ≤ 5) :
      Nat.Coprime q p := by
    exact (hp.coprime_iff_not_dvd.mpr (by
      intro hpdvd
      have hple : p ≤ q :=
        Nat.le_of_dvd hq.pos hpdvd
      omega)).symm
  have hnotTwo : ¬2 ∣ Nat.card C := by
    exact himpossible (q := 2) (by norm_num)
      (hcoprimeSmallPrime 2 (by norm_num) (by norm_num))
  have hnotThree : ¬3 ∣ Nat.card C := by
    exact himpossible (q := 3) (by norm_num)
      (hcoprimeSmallPrime 3 (by norm_num) (by norm_num))
  have hnotFive : ¬5 ∣ Nat.card C := by
    exact himpossible (q := 5) (by norm_num)
      (hcoprimeSmallPrime 5 (by norm_num) (by norm_num))
  have hcoprimeSixteen : Nat.Coprime (Nat.card C) (2 ^ 4) :=
    Nat.prime_two.coprime_pow_of_not_dvd hnotTwo
  have hcoprimeNine : Nat.Coprime (Nat.card C) (3 ^ 2) :=
    Nat.prime_three.coprime_pow_of_not_dvd hnotThree
  have hcoprimeFive : Nat.Coprime (Nat.card C) 5 :=
    ((show Nat.Prime 5 by norm_num).coprime_iff_not_dvd.mpr hnotFive).symm
  have hcoprimeSevenTwenty : Nat.Coprime (Nat.card C) 720 := by
    rw [show 720 = 5 * (3 ^ 2 * 2 ^ 4) by norm_num]
    exact hcoprimeFive.mul_right
      (hcoprimeNine.mul_right hcoprimeSixteen)
  have hfactorialDvd : f.factorial ∣ 720 := by
    interval_cases f <;> norm_num
  have hCdivSevenTwenty : Nat.card C ∣ 720 * p :=
    hCdiv.trans (Nat.mul_dvd_mul_right hfactorialDvd p)
  have hCdvdP : Nat.card C ∣ p :=
    hcoprimeSevenTwenty.dvd_of_dvd_mul_left hCdivSevenTwenty
  exact Nat.dvd_antisymm hCdvdP hpdivC

end FiveTransitive.FewFixedPrimeCycle

end CFSG
