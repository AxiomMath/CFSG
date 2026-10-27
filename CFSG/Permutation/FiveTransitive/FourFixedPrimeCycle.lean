module

public import CFSG.Permutation.FiveTransitive.Degree15FourTuples
public import Mathlib.CategoryTheory.Action.Concrete

public section

namespace CFSG

namespace FiveTransitive.FourFixedPrimeCycle

open MulAction SubMulAction Subgroup

private theorem centralizer_card_eq_prime_of_not_alternating
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    {p : ℕ} (hp : p.Prime) (hpFive : 5 ≤ p)
    (hcard : Fintype.card X = p + 4)
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
        ({g} : Set (Equiv.Perm X))) = 24 * p := by
    rw [Equiv.Perm.nat_card_centralizer, hgcycle.cycleType,
      hgsupport, hcard]
    simp [hp.ne_zero]
    ring
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
  have hCdiv : Nat.card C ∣ 24 * p := by
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
    have hsuppCard : w.support.card ≤ 4 := by
      calc
        w.support.card ≤ g.supportᶜ.card :=
          Finset.card_le_card hsuppSubset
        _ = Fintype.card X - g.support.card := by
          rw [Finset.card_compl]
        _ = 4 := by
          rw [hcard, hgsupport]
          omega
    have hwNe : w ≠ 1 := by
      intro hw
      rw [hw, orderOf_one] at hworder
      exact hq.ne_one hworder.symm
    exact hnotAlt
      (Helpers.alternatingGroup_le_of_nontrivial_card_support_le_five
        X P h5 (by omega) (v : P).prop hwNe (by
          change w.support.card ≤ 5
          omega))
  have hnotTwo : ¬2 ∣ Nat.card C := by
    exact himpossible (q := 2) (by norm_num)
      ((hp.coprime_iff_not_dvd.mpr (by
        intro htwo
        have hple : p ≤ 2 :=
          Nat.le_of_dvd (by norm_num) htwo
        omega)).symm)
  have hnotThree : ¬3 ∣ Nat.card C := by
    exact himpossible (q := 3) (by norm_num)
      ((hp.coprime_iff_not_dvd.mpr (by
        intro hthree
        have hple : p ≤ 3 :=
          Nat.le_of_dvd (by norm_num) hthree
        omega)).symm)
  have hcoprimeEight : Nat.Coprime (Nat.card C) (2 ^ 3) :=
    Nat.prime_two.coprime_pow_of_not_dvd hnotTwo
  have hcoprimeThree : Nat.Coprime (Nat.card C) 3 :=
    (Nat.prime_three.coprime_iff_not_dvd.mpr hnotThree).symm
  have hcoprimeTwentyFour : Nat.Coprime (Nat.card C) 24 := by
    rw [show 24 = 3 * 2 ^ 3 by norm_num]
    exact hcoprimeThree.mul_right hcoprimeEight
  have hCdvdP : Nat.card C ∣ p :=
    hcoprimeTwentyFour.dvd_of_dvd_mul_left hCdiv
  exact Nat.dvd_antisymm hCdvdP hpdivC

theorem card_conjugacy_orbit_mul_prime
    {P : Type} [Group P] [Fintype P]
    {p : ℕ} (u : P)
    (hcentralizer :
      Nat.card (Subgroup.centralizer ({u} : Set P)) = p) :
    Nat.card (MulAction.orbit (ConjAct P) u) * p =
      Nat.card P := by
  classical
  letI : Fintype (MulAction.orbit (ConjAct P) u) :=
    Fintype.ofFinite _
  letI :
      Fintype (MulAction.stabilizer (ConjAct P) u) :=
    Fintype.ofFinite _
  have hstabilizer :
      Fintype.card (MulAction.stabilizer (ConjAct P) u) = p := by
    rw [← Nat.card_eq_fintype_card,
      ← Subgroup.nat_card_centralizer_nat_card_stabilizer]
    exact hcentralizer
  have horbitCard :=
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group
      (ConjAct P) u
  rw [hstabilizer, ConjAct.card,
    ← Nat.card_eq_fintype_card] at horbitCard
  simpa only [Nat.card_eq_fintype_card] using horbitCard

private theorem card_fixedBy_four_of_mem_conjugacy_orbit
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    {p : ℕ} (hp : p.Prime) (hpFive : 5 ≤ p)
    (hcard : Fintype.card X = p + 4)
    (u : P) (huorder : orderOf u = p)
    (a : MulAction.orbit (ConjAct P) u) :
    Fintype.card
      (MulAction.fixedBy (Fin 4 ↪ X) (a.1 : P)) = 24 := by
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
      ((a.1 : P) : Equiv.Perm X).support.card = p := by
    calc
      ((a.1 : P) : Equiv.Perm X).support.card =
          (((q : P) : Equiv.Perm X) *
            ((a.1 : P) : Equiv.Perm X) *
            ((q : P) : Equiv.Perm X)⁻¹).support.card :=
        Equiv.Perm.card_support_conj.symm
      _ = g.support.card := by rw [hconjPerm]
      _ = p := hgsupport
  have hfixedX :
      Fintype.card
        (MulAction.fixedBy X (a.1 : P)) = 4 := by
    rw [Degree15.card_fixedBy_subgroup_perm, hcard,
      hasupport]
    omega
  calc
    Fintype.card
        (MulAction.fixedBy (Fin 4 ↪ X) (a.1 : P)) =
        (Fintype.card
          (MulAction.fixedBy X (a.1 : P))).descFactorial
            (Fintype.card (Fin 4)) :=
      Degree15.card_fixedBy_embedding (a.1 : P)
    _ = 24 := by
      rw [hfixedX, Fintype.card_fin]
      norm_num [Nat.descFactorial]

theorem alternatingGroup_le_of_prime_dvd_card
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    {p : ℕ} (hp : p.Prime) (hpFive : 5 ≤ p) (hpLt : p < 24)
    (hcard : Fintype.card X = p + 4)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hpdiv : p ∣ Nat.card P) :
    alternatingGroup X ≤ P := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨u, huorder⟩ :=
    exists_prime_orderOf_dvd_card' p hpdiv
  by_contra hnotAlt
  have hcentralizer :
      Nat.card (Subgroup.centralizer ({u} : Set P)) = p :=
    centralizer_card_eq_prime_of_not_alternating
      X P hp hpFive hcard h5 hnotAlt u huorder
  let A := MulAction.orbit (ConjAct P) u
  letI : Fintype A := Fintype.ofFinite _
  let val : A → P := fun a => a.1
  have hvalInjective : Function.Injective val :=
    Subtype.val_injective
  have hAcard :
      Fintype.card A * p = Nat.card P := by
    simpa [A, Nat.card_eq_fintype_card] using
      card_conjugacy_orbit_mul_prime u hcentralizer
  have hfixed (a : A) :
      Fintype.card
          (MulAction.fixedBy (Fin 4 ↪ X) (val a)) = 24 :=
    card_fixedBy_four_of_mem_conjugacy_orbit
      X P hp hpFive hcard u huorder a
  have hselectedSum :
      (∑ a : A,
          Fintype.card
            (MulAction.fixedBy (Fin 4 ↪ X) (val a))) =
        Fintype.card A * 24 := by
    simp_rw [hfixed]
    simp
  have hselectedLe :
      (∑ a : A,
          Fintype.card
            (MulAction.fixedBy (Fin 4 ↪ X) (val a))) ≤
        ∑ q : P,
          Fintype.card
            (MulAction.fixedBy (Fin 4 ↪ X) q) := by
    calc
      (∑ a : A,
          Fintype.card
            (MulAction.fixedBy (Fin 4 ↪ X) (val a))) =
          ∑ q ∈ Finset.univ.image val,
            Fintype.card
              (MulAction.fixedBy (Fin 4 ↪ X) q) := by
        rw [Finset.sum_image hvalInjective.injOn]
      _ ≤ ∑ q ∈ (Finset.univ : Finset P),
          Fintype.card
            (MulAction.fixedBy (Fin 4 ↪ X) q) :=
        Finset.sum_le_sum_of_subset (by simp)
      _ = ∑ q : P,
          Fintype.card
            (MulAction.fixedBy (Fin 4 ↪ X) q) := by
        simp
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨g, hg⟩ := h5 a b a.injective b.injective
    refine ⟨g, ?_⟩
    ext i
    exact hg i
  have hP4 : MulAction.IsMultiplyPretransitive P X 4 := by
    letI : MulAction.IsMultiplyPretransitive P X 5 := hP5
    exact MulAction.isMultiplyPretransitive_of_le
      (G := P) (α := X) (m := 4) (n := 5) (by omega) (by
        rw [Nat.card_eq_fintype_card, hcard]
        omega)
  letI : MulAction.IsMultiplyPretransitive P X 4 := hP4
  letI : Nonempty (Fin 4 ↪ X) :=
    Fintype.card_pos_iff.mp (by
      rw [Fintype.card_embedding_eq, Fintype.card_fin, hcard]
      rw [Nat.descFactorial_pos]
      omega)
  letI : Unique
      (MulAction.orbitRel.Quotient P (Fin 4 ↪ X)) :=
    Classical.choice
      ((MulAction.pretransitive_iff_unique_quotient_of_nonempty
        P (Fin 4 ↪ X)).mp hP4)
  have hburnside :=
    MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
      P (Fin 4 ↪ X)
  have hburnside' :
      (∑ q : P,
          Fintype.card
            (MulAction.fixedBy (Fin 4 ↪ X) q)) =
        Nat.card P := by
    rw [Fintype.card_unique, one_mul,
      ← Nat.card_eq_fintype_card] at hburnside
    exact hburnside
  have hoverfill : Fintype.card A * 24 ≤ Nat.card P := by
    calc
      Fintype.card A * 24 =
          ∑ a : A,
            Fintype.card
              (MulAction.fixedBy (Fin 4 ↪ X) (val a)) :=
        hselectedSum.symm
      _ ≤ ∑ q : P,
          Fintype.card
            (MulAction.fixedBy (Fin 4 ↪ X) q) :=
        hselectedLe
      _ = Nat.card P := hburnside'
  rw [← hAcard] at hoverfill
  have hApos : 0 < Fintype.card A :=
    Fintype.card_pos_iff.mpr
      ⟨⟨u, MulAction.mem_orbit_self u⟩⟩
  nlinarith

end FiveTransitive.FourFixedPrimeCycle

end CFSG
