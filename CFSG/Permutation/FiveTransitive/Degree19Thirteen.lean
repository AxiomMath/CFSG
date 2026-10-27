module

public import CFSG.Permutation.FiveTransitive.Degree19SupportSix
public import CFSG.Permutation.FiveTransitive.FourFixedPrimeCycle

public section

namespace CFSG

namespace FiveTransitive.Degree19

open MulAction SubMulAction Subgroup

private theorem thirteen_cycle_centralizer_card_eq_thirteen
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 19)
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
        ({g} : Set (Equiv.Perm X))) = 9360 := by
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
  have hCdiv : Nat.card C ∣ 9360 := by
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
    have hsuppCard : w.support.card ≤ 6 := by
      calc
        w.support.card ≤ g.supportᶜ.card :=
          Finset.card_le_card hsuppSubset
        _ = 19 - 13 := by
          rw [Finset.card_compl, hgsupport, hcard]
        _ = 6 := by norm_num
    have hwNe : w ≠ 1 := by
      intro hw
      rw [hw, orderOf_one] at hworder
      exact hq.ne_one hworder.symm
    apply hnotAlt
    by_cases hsmall : w.support.card ≤ 5
    · exact
        Helpers.alternatingGroup_le_of_nontrivial_card_support_le_five
          X P h5 (by omega) (v : P).prop hwNe hsmall
    · have hsix : w.support.card = 6 := by omega
      exact alternatingGroup_le_of_prime_order_support_six
        X P hcard h5 (v : P).prop hq hworder hsix
  have hnotTwo : ¬2 ∣ Nat.card C :=
    himpossible (q := 2) (by norm_num) (by norm_num)
  have hnotThree : ¬3 ∣ Nat.card C :=
    himpossible (q := 3) (by norm_num) (by norm_num)
  have hnotFive : ¬5 ∣ Nat.card C :=
    himpossible (q := 5) (by norm_num) (by norm_num)
  have hcoprimeSixteen : Nat.Coprime (Nat.card C) (2 ^ 4) :=
    Nat.prime_two.coprime_pow_of_not_dvd hnotTwo
  have hcoprimeNine : Nat.Coprime (Nat.card C) (3 ^ 2) :=
    Nat.prime_three.coprime_pow_of_not_dvd hnotThree
  have hcoprimeFive : Nat.Coprime (Nat.card C) 5 :=
    ((show Nat.Prime 5 by norm_num).coprime_iff_not_dvd.mpr
      hnotFive).symm
  have hcoprimeSevenTwenty :
      Nat.Coprime (Nat.card C) 720 := by
    rw [show 720 = 5 * (3 ^ 2 * 2 ^ 4) by norm_num]
    exact hcoprimeFive.mul_right
      (hcoprimeNine.mul_right hcoprimeSixteen)
  have hCdvdThirteen : Nat.card C ∣ 13 := by
    apply hcoprimeSevenTwenty.dvd_of_dvd_mul_left
    norm_num at hCdiv ⊢
    exact hCdiv
  exact Nat.dvd_antisymm hCdvdThirteen h13divC

private theorem card_fixedBy_five_of_mem_thirteen_conjugacy_orbit
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 19)
    (u : P) (huorder : orderOf u = 13)
    (a : MulAction.orbit (ConjAct P) u) :
    Fintype.card
      (MulAction.fixedBy (Fin 5 ↪ X) (a.1 : P)) = 720 := by
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
      ((a.1 : P) : Equiv.Perm X).support.card = 13 := by
    calc
      ((a.1 : P) : Equiv.Perm X).support.card =
          (((q : P) : Equiv.Perm X) *
            ((a.1 : P) : Equiv.Perm X) *
            ((q : P) : Equiv.Perm X)⁻¹).support.card :=
        Equiv.Perm.card_support_conj.symm
      _ = g.support.card := by rw [hconjPerm]
      _ = 13 := hgsupport
  have hfixedX :
      Fintype.card
        (MulAction.fixedBy X (a.1 : P)) = 6 := by
    rw [Degree15.card_fixedBy_subgroup_perm, hcard,
      hasupport]
  calc
    Fintype.card
        (MulAction.fixedBy (Fin 5 ↪ X) (a.1 : P)) =
        (Fintype.card
          (MulAction.fixedBy X (a.1 : P))).descFactorial
            (Fintype.card (Fin 5)) :=
      Degree15.card_fixedBy_embedding (a.1 : P)
    _ = 720 := by
      rw [hfixedX, Fintype.card_fin]
      norm_num [Nat.descFactorial]

theorem thirteen_not_dvd_card_of_not_alternating
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 19)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P) :
    ¬13 ∣ Nat.card P := by
  classical
  intro h13
  letI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨u, huorder⟩ :=
    exists_prime_orderOf_dvd_card' 13 h13
  have hcentralizer :
      Nat.card (Subgroup.centralizer ({u} : Set P)) = 13 :=
    thirteen_cycle_centralizer_card_eq_thirteen
      X P hcard h5 hnotAlt u huorder
  let A := MulAction.orbit (ConjAct P) u
  letI : Fintype A := Fintype.ofFinite _
  let val : A → P := fun a => a.1
  have hvalInjective : Function.Injective val :=
    Subtype.val_injective
  have hAcard :
      Fintype.card A * 13 = Nat.card P := by
    simpa [A, Nat.card_eq_fintype_card] using
      FourFixedPrimeCycle.card_conjugacy_orbit_mul_prime
        u hcentralizer
  have hfixed (a : A) :
      Fintype.card
          (MulAction.fixedBy (Fin 5 ↪ X) (val a)) = 720 :=
    card_fixedBy_five_of_mem_thirteen_conjugacy_orbit
      X P hcard u huorder a
  have hselectedSum :
      (∑ a : A,
          Fintype.card
            (MulAction.fixedBy (Fin 5 ↪ X) (val a))) =
        Fintype.card A * 720 := by
    simp_rw [hfixed]
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
    obtain ⟨g, hg⟩ := h5 a b a.injective b.injective
    refine ⟨g, ?_⟩
    ext i
    exact hg i
  letI : MulAction.IsMultiplyPretransitive P X 5 := hP5
  letI : Nonempty (Fin 5 ↪ X) :=
    Fintype.card_pos_iff.mp (by
      rw [Fintype.card_embedding_eq, Fintype.card_fin, hcard]
      norm_num)
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
  have hoverfill : Fintype.card A * 720 ≤ Nat.card P := by
    calc
      Fintype.card A * 720 =
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

end FiveTransitive.Degree19

end CFSG
