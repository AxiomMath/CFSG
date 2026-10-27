module

public import CFSG.Permutation.FiveTransitive.Degree15FourTuples
public import CFSG.Permutation.FiveTransitive.Degree25SmallSupport
public import Mathlib.CategoryTheory.Action.Concrete

public section

namespace CFSG

namespace FiveTransitive.Degree25

open MulAction SubMulAction Subgroup

private theorem centralizer_card_le_two_thousand_one_hundred_seventy_six
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (u : P) (huorder : orderOf u = 17) :
    Nat.card (Subgroup.centralizer ({u} : Set P)) ≤ 2176 := by
  classical
  let g : Equiv.Perm X := u
  have hgorder : orderOf g = 17 := by
    calc
      orderOf g = orderOf u := Subgroup.orderOf_coe _
      _ = 17 := huorder
  have hgcycle : g.IsCycle := by
    apply Equiv.Perm.isCycle_of_prime_order'
    · rw [hgorder]
      norm_num
    · rw [hcard, hgorder]
      norm_num
  have hgsupport : g.support.card = 17 := by
    rw [← hgcycle.orderOf, hgorder]
  have hcentralizerPerm :
      Nat.card (Subgroup.centralizer
        ({g} : Set (Equiv.Perm X))) = 40320 * 17 := by
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
  have hCdiv : Nat.card C ∣ 40320 * 17 := by
    rw [← hcentralizerPerm]
    exact Subgroup.card_dvd_of_injective
      centMap hcentMapInjective
  have himpossible {q : ℕ} (hq : q.Prime)
      (hqcop : Nat.Coprime q 17)
      (hqnotEight : ¬q ∣ 8)
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
    have hsuppCard : w.support.card ≤ 8 := by
      calc
        w.support.card ≤ g.supportᶜ.card :=
          Finset.card_le_card hsuppSubset
        _ = Fintype.card X - g.support.card := by
          rw [Finset.card_compl]
        _ = 8 := by
          rw [hcard, hgsupport]
    have hwprime : (orderOf w).Prime := by
      rw [hworder]
      exact hq
    obtain ⟨m, hm⟩ :=
      Equiv.Perm.cycleType_prime_order hwprime
    have hqdvdSupport : q ∣ w.support.card := by
      rw [← w.sum_cycleType, hm, Multiset.sum_replicate,
        nsmul_eq_mul, Nat.cast_id, hworder]
      exact dvd_mul_left q (m + 1)
    have hsuppSeven : w.support.card ≤ 7 := by
      by_contra hnot
      have height : w.support.card = 8 := by omega
      exact hqnotEight (by
        rwa [height] at hqdvdSupport)
    have hwNe : w ≠ 1 := by
      intro hw
      rw [hw, orderOf_one] at hworder
      exact hq.ne_one hworder.symm
    exact hnotAlt
      (alternatingGroup_le_of_nontrivial_support_le_seven
        X P hcard h5 (v : P).prop hwNe (by
          simpa only [w] using hsuppSeven))
  have hnotThree : ¬3 ∣ Nat.card C :=
    himpossible (q := 3) (by norm_num) (by norm_num)
      (by norm_num)
  have hnotFive : ¬5 ∣ Nat.card C :=
    himpossible (q := 5) (by norm_num) (by norm_num)
      (by norm_num)
  have hnotSeven : ¬7 ∣ Nat.card C :=
    himpossible (q := 7) (by norm_num) (by norm_num)
      (by norm_num)
  have hcoprimeThree : Nat.Coprime (Nat.card C) (3 ^ 2) :=
    Nat.prime_three.coprime_pow_of_not_dvd hnotThree
  have hcoprimeFive : Nat.Coprime (Nat.card C) 5 :=
    ((show Nat.Prime 5 by norm_num).coprime_iff_not_dvd.mpr
      hnotFive).symm
  have hcoprimeSeven : Nat.Coprime (Nat.card C) 7 :=
    ((show Nat.Prime 7 by norm_num).coprime_iff_not_dvd.mpr
      hnotSeven).symm
  have hcoprime315 : Nat.Coprime (Nat.card C) 315 := by
    rw [show 315 = 7 * (5 * 3 ^ 2) by norm_num]
    exact hcoprimeSeven.mul_right
      (hcoprimeFive.mul_right hcoprimeThree)
  have hCdiv' : Nat.card C ∣ 315 * 2176 := by
    norm_num at hCdiv ⊢
    exact hCdiv
  have hCdvd : Nat.card C ∣ 2176 :=
    hcoprime315.dvd_of_dvd_mul_left hCdiv'
  exact Nat.le_of_dvd (by norm_num) hCdvd

private theorem card_fixedBy_five_eq_six_thousand_seven_hundred_twenty_of_order_seventeen
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (u : P) (huorder : orderOf u = 17)
    (a : MulAction.orbit (ConjAct P) u) :
    Fintype.card
      (MulAction.fixedBy (Fin 5 ↪ X) (a.1 : P)) = 6720 := by
  classical
  let g : Equiv.Perm X := u
  have hgorder : orderOf g = 17 := by
    calc
      orderOf g = orderOf u := Subgroup.orderOf_coe _
      _ = 17 := huorder
  have hgcycle : g.IsCycle := by
    apply Equiv.Perm.isCycle_of_prime_order'
    · rw [hgorder]
      norm_num
    · rw [hcard, hgorder]
      norm_num
  have hgsupport : g.support.card = 17 := by
    rw [← hgcycle.orderOf, hgorder]
  obtain ⟨q, hq⟩ :=
    isConj_iff.mp
      (ConjAct.mem_orbit_conjAct.mp a.prop)
  have hconjPerm :
      ((q : P) : Equiv.Perm X) *
            ((a.1 : P) : Equiv.Perm X) *
            ((q : P) : Equiv.Perm X)⁻¹ =
          g :=
    congrArg Subtype.val hq
  have hasupport :
      ((a.1 : P) : Equiv.Perm X).support.card = 17 := by
    calc
      ((a.1 : P) : Equiv.Perm X).support.card =
          (((q : P) : Equiv.Perm X) *
            ((a.1 : P) : Equiv.Perm X) *
            ((q : P) : Equiv.Perm X)⁻¹).support.card :=
        Equiv.Perm.card_support_conj.symm
      _ = g.support.card := by rw [hconjPerm]
      _ = 17 := hgsupport
  have hfixedX :
      Fintype.card
        (MulAction.fixedBy X (a.1 : P)) = 8 := by
    rw [Degree15.card_fixedBy_subgroup_perm, hcard,
      hasupport]
  calc
    Fintype.card
        (MulAction.fixedBy (Fin 5 ↪ X) (a.1 : P)) =
        (Fintype.card
          (MulAction.fixedBy X (a.1 : P))).descFactorial
            (Fintype.card (Fin 5)) :=
      Degree15.card_fixedBy_embedding (a.1 : P)
    _ = 6720 := by
      rw [hfixedX, Fintype.card_fin]
      norm_num [Nat.descFactorial]

private theorem conjugacy_class_overfill_of_five_transitive
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hcardFive : 5 ≤ Fintype.card X)
    (u : P) (m : ℕ)
    (hfixed : ∀ a : MulAction.orbit (ConjAct P) u,
      Fintype.card
        (MulAction.fixedBy (Fin 5 ↪ X) (a.1 : P)) = m)
    (hcentralizerLt :
      Nat.card (Subgroup.centralizer ({u} : Set P)) < m) :
    False := by
  classical
  let A := MulAction.orbit (ConjAct P) u
  letI : Fintype A := Fintype.ofFinite _
  let val : A → P := fun a => a.1
  have hvalInjective : Function.Injective val :=
    Subtype.val_injective
  have hstabilizer :
      Fintype.card (MulAction.stabilizer (ConjAct P) u) =
        Nat.card (Subgroup.centralizer ({u} : Set P)) := by
    rw [← Nat.card_eq_fintype_card,
      ← Subgroup.nat_card_centralizer_nat_card_stabilizer]
  have hAcard :
      Fintype.card A *
          Nat.card (Subgroup.centralizer ({u} : Set P)) =
        Nat.card P := by
    have horbit :=
      MulAction.card_orbit_mul_card_stabilizer_eq_card_group
        (ConjAct P) u
    rw [hstabilizer, ConjAct.card,
      ← Nat.card_eq_fintype_card] at horbit
    simpa only [A, Nat.card_eq_fintype_card] using horbit
  have hselectedSum :
      (∑ a : A,
          Fintype.card
            (MulAction.fixedBy (Fin 5 ↪ X) (val a))) =
        Fintype.card A * m := by
    simp_rw [show ∀ a : A,
      Fintype.card
        (MulAction.fixedBy (Fin 5 ↪ X) (val a)) = m by
          intro a
          simpa only [val] using hfixed a]
    simp
  have hselectedLe :
      (∑ a : A,
          Fintype.card
            (MulAction.fixedBy (Fin 5 ↪ X) (val a))) ≤
        ∑ q : P,
          Fintype.card
            (MulAction.fixedBy (Fin 5 ↪ X) q) := by
    calc
      (∑ a : A,
          Fintype.card
            (MulAction.fixedBy (Fin 5 ↪ X) (val a))) =
          ∑ q ∈ Finset.univ.image val,
            Fintype.card
              (MulAction.fixedBy (Fin 5 ↪ X) q) := by
        rw [Finset.sum_image hvalInjective.injOn]
      _ ≤ ∑ q ∈ (Finset.univ : Finset P),
          Fintype.card
            (MulAction.fixedBy (Fin 5 ↪ X) q) :=
        Finset.sum_le_sum_of_subset (by simp)
      _ = ∑ q : P,
          Fintype.card
            (MulAction.fixedBy (Fin 5 ↪ X) q) := by
        simp
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g, hg⟩ :=
      h5 a b a.injective b.injective
    refine ⟨g, ?_⟩
    ext i
    exact hg i
  letI : MulAction.IsMultiplyPretransitive P X 5 := hP5
  letI : Nonempty (Fin 5 ↪ X) :=
    Fintype.card_pos_iff.mp (by
      rw [Fintype.card_embedding_eq, Fintype.card_fin]
      exact Nat.descFactorial_pos.mpr hcardFive)
  letI : Unique
      (MulAction.orbitRel.Quotient P (Fin 5 ↪ X)) :=
    Classical.choice
      ((MulAction.pretransitive_iff_unique_quotient_of_nonempty
        P (Fin 5 ↪ X)).mp hP5)
  have hburnside :=
    MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
      P (Fin 5 ↪ X)
  have hburnside' :
      (∑ q : P,
          Fintype.card
            (MulAction.fixedBy (Fin 5 ↪ X) q)) =
        Nat.card P := by
    rw [Fintype.card_unique, one_mul,
      ← Nat.card_eq_fintype_card] at hburnside
    exact hburnside
  have hoverfill :
      Fintype.card A * m ≤ Nat.card P := by
    calc
      Fintype.card A * m =
          ∑ a : A,
            Fintype.card
              (MulAction.fixedBy (Fin 5 ↪ X) (val a)) :=
        hselectedSum.symm
      _ ≤ ∑ q : P,
          Fintype.card
            (MulAction.fixedBy (Fin 5 ↪ X) q) :=
        hselectedLe
      _ = Nat.card P := hburnside'
  rw [← hAcard] at hoverfill
  have hApos : 0 < Fintype.card A :=
    Fintype.card_pos_iff.mpr
      ⟨⟨u, MulAction.mem_orbit_self u⟩⟩
  nlinarith

theorem seventeen_not_dvd_card_of_not_alternating
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P) :
    ¬17 ∣ Nat.card P := by
  classical
  intro hseventeen
  letI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  obtain ⟨u, huorder⟩ :=
    exists_prime_orderOf_dvd_card' 17 hseventeen
  have hcentralizerLe :
      Nat.card
          (Subgroup.centralizer ({u} : Set P)) ≤ 2176 :=
    centralizer_card_le_two_thousand_one_hundred_seventy_six
      X P hcard h5 hnotAlt u huorder
  exact conjugacy_class_overfill_of_five_transitive
    X P h5 (by omega) u 6720
      (card_fixedBy_five_eq_six_thousand_seven_hundred_twenty_of_order_seventeen
        X P hcard u huorder)
      (by omega)

end FiveTransitive.Degree25

end CFSG
