module

public import CFSG.Permutation.FiveTransitive.Degree15FourTuples
public import CFSG.Permutation.FiveTransitive.Degree20SmallSupport
public import Mathlib.CategoryTheory.Action.Concrete

public section

namespace CFSG

namespace FiveTransitive.Degree20

open MulAction SubMulAction Subgroup

private theorem eleven_centralizer_arithmetic
    {k : ℕ} (hk : k ∣ 114048) (hnot : ¬27 ∣ k) :
    k ≤ 12672 := by
  by_contra hle
  have hklarge : 12673 ≤ k := by omega
  obtain ⟨c, hc⟩ := hk
  have hcpos : 0 < c := by
    by_contra hc0
    simp only [not_lt, nonpos_iff_eq_zero] at hc0
    subst c
    norm_num at hc
  have hclt : c < 9 := by
    by_contra hc9
    have hprod : 12673 * 9 ≤ k * c :=
      Nat.mul_le_mul hklarge (by omega)
    rw [← hc] at hprod
    norm_num at hprod
  apply hnot
  interval_cases c <;> norm_num at hc ⊢ <;> omega

private theorem eleven_cycle_centralizer_card_le
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 20)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (u : P) (huorder : orderOf u = 11) :
    Nat.card (Subgroup.centralizer ({u} : Set P)) ≤ 12672 := by
  classical
  let g : Equiv.Perm X := u
  have hgorder : orderOf g = 11 := by
    calc
      orderOf g = orderOf u := Subgroup.orderOf_coe _
      _ = 11 := huorder
  have hgcycle : g.IsCycle :=
    Equiv.Perm.isCycle_of_prime_order' (by
      rw [hgorder]
      norm_num) (by
        rw [hcard, hgorder]
        norm_num)
  have hgsupport : g.support.card = 11 := by
    rw [← hgcycle.orderOf, hgorder]
  have hcentralizerPerm :
      Nat.card (Subgroup.centralizer
        ({g} : Set (Equiv.Perm X))) = 3991680 := by
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
  have hCdiv : Nat.card C ∣ 3991680 := by
    rw [← hcentralizerPerm]
    exact Subgroup.card_dvd_of_injective
      centMap hcentMapInjective
  have himpossible {q : ℕ} (hq : q.Prime)
      (hqcases : q = 5 ∨ q = 7)
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
      rcases hqcases with rfl | rfl <;> norm_num
    have hsuppSubset :=
      PermCentralizer.support_le_compl_of_isCycle_of_commute_of_coprime_order
        hgcycle hcomm hcoprime
    have hsuppCard : w.support.card ≤ 9 := by
      calc
        w.support.card ≤ g.supportᶜ.card :=
          Finset.card_le_card hsuppSubset
        _ = 20 - 11 := by
          rw [Finset.card_compl, hgsupport, hcard]
        _ = 9 := by norm_num
    have hwprime : (orderOf w).Prime := by
      rw [hworder]
      exact hq
    obtain ⟨m, hm⟩ :=
      Equiv.Perm.cycleType_prime_order hwprime
    have hsum := w.sum_cycleType
    rw [hm, Multiset.sum_replicate, nsmul_eq_mul,
      Nat.cast_id, hworder] at hsum
    have hwNe : w ≠ 1 := by
      intro hw
      rw [hw, orderOf_one] at hworder
      exact hq.ne_one hworder.symm
    apply hnotAlt
    have hsmall : w.support.card ≤ 7 := by
      rcases hqcases with rfl | rfl <;> omega
    exact alternatingGroup_le_of_nontrivial_support_le_seven
      X P hcard h5 (v : P).prop hwNe hsmall
  have hnotFive : ¬5 ∣ Nat.card C :=
    himpossible (q := 5) (by norm_num) (Or.inl rfl)
  have hnotSeven : ¬7 ∣ Nat.card C :=
    himpossible (q := 7) (by norm_num) (Or.inr rfl)
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let S : Sylow 3 C := Sylow.nonempty.some
  have hScardLe : Nat.card S ≤ 9 := by
    let F := MulAction.fixedBy X u
    have hFcard : Fintype.card F = 9 := by
      rw [Degree15.card_fixedBy_subgroup_perm,
        hcard, hgsupport]
    let x : F :=
      Classical.choice
        (Fintype.card_pos_iff.mp (by
          rw [hFcard]
          norm_num))
    let R : Subgroup S :=
      MulAction.stabilizer S (x : X)
    have hRbot : R = ⊥ := by
      by_contra hRne
      have hRnontrivial : Nontrivial R :=
        R.nontrivial_iff_ne_bot.mpr hRne
      have hRpgroup : IsPGroup 3 R :=
        S.2.to_subgroup R
      have hRcardNeOne : Nat.card R ≠ 1 :=
        (Finite.one_lt_card_iff_nontrivial.mpr
          hRnontrivial).ne'
      have hthreeDvdR : 3 ∣ Nat.card R :=
        hRpgroup.card_eq_or_dvd.resolve_left hRcardNeOne
      obtain ⟨v, hvorder⟩ :=
        exists_prime_orderOf_dvd_card'
          (G := R) 3 hthreeDvdR
      let vS : S := v
      let vC : C := vS
      let vP : P := vC
      let w : Equiv.Perm X := vP
      have hworder : orderOf w = 3 := by
        calc
          orderOf w = orderOf vP :=
            Subgroup.orderOf_coe _
          _ = orderOf vC :=
            Subgroup.orderOf_coe _
          _ = orderOf vS :=
            Subgroup.orderOf_coe _
          _ = orderOf v :=
            Subgroup.orderOf_coe _
          _ = 3 := hvorder
      have hcomm : Commute w g :=
        congrArg Subtype.val
          (Subgroup.mem_centralizer_singleton_iff.mp
            vC.prop)
      have hcoprime :
          Nat.Coprime (orderOf w) (orderOf g) := by
        rw [hworder, hgorder]
        norm_num
      have hsuppSubset :
          w.support ⊆ g.supportᶜ :=
        PermCentralizer.support_le_compl_of_isCycle_of_commute_of_coprime_order
          hgcycle hcomm hcoprime
      have hxcomp : (x : X) ∈ g.supportᶜ := by
        rw [Finset.mem_compl,
          Equiv.Perm.notMem_support]
        exact x.prop
      have hvfix :
          vS • (x : X) = (x : X) :=
        MulAction.mem_stabilizer_iff.mp v.prop
      have hvfix' :
          w (x : X) = (x : X) := by
        change vS • (x : X) = (x : X)
        exact hvfix
      have hxnot : (x : X) ∉ w.support := by
        rw [Equiv.Perm.notMem_support]
        exact hvfix'
      have hsuppProper :
          w.support ⊂ g.supportᶜ := by
        refine Finset.ssubset_iff_subset_ne.mpr
          ⟨hsuppSubset, ?_⟩
        intro heq
        apply hxnot
        rw [heq]
        exact hxcomp
      have hsuppCard : w.support.card ≤ 8 := by
        have hlt := Finset.card_lt_card hsuppProper
        have hcompCard : g.supportᶜ.card = 9 := by
          rw [Finset.card_compl, hcard, hgsupport]
        omega
      have hwprime : (orderOf w).Prime := by
        rw [hworder]
        norm_num
      obtain ⟨m, hm⟩ :=
        Equiv.Perm.cycleType_prime_order hwprime
      have hsum := w.sum_cycleType
      rw [hm, Multiset.sum_replicate, nsmul_eq_mul,
        Nat.cast_id, hworder] at hsum
      have hwNe : w ≠ 1 := by
        intro hw
        rw [hw, orderOf_one] at hworder
        norm_num at hworder
      have hsuppSix : w.support.card ≤ 6 := by
        omega
      exact hnotAlt
        (alternatingGroup_le_of_nontrivial_support_le_seven
          X P hcard h5 vP.prop hwNe
            (hsuppSix.trans (by omega)))
    have hRcard : Fintype.card R = 1 := by
      calc
        Fintype.card R =
            Fintype.card (⊥ : Subgroup S) :=
          Fintype.card_congr
            (MulEquiv.subgroupCongr hRbot).toEquiv
        _ = 1 := by simp
    have horbit :=
      MulAction.card_orbit_mul_card_stabilizer_eq_card_group
        S (x : X)
    change
      Fintype.card (MulAction.orbit S (x : X)) *
          Fintype.card R =
        Fintype.card S at horbit
    rw [hRcard, mul_one] at horbit
    have horbitFixed
        (y : MulAction.orbit S (x : X)) :
        y.1 ∈ F := by
      obtain ⟨s, hs⟩ :=
        MulAction.mem_orbit_iff.mp y.prop
      let sP : P := ((s : S) : C)
      have hscomm : Commute sP u :=
        Subgroup.mem_centralizer_singleton_iff.mp
          ((s : S) : C).prop
      have hfixP :
          (u : P) • (sP • (x : X)) =
            sP • (x : X) := by
        calc
          (u : P) • (sP • (x : X)) =
              ((u : P) * sP) • (x : X) :=
            (mul_smul _ _ _).symm
          _ = (sP * (u : P)) • (x : X) := by
            rw [hscomm.eq.symm]
          _ = sP • ((u : P) • (x : X)) :=
            mul_smul _ _ _
          _ = sP • (x : X) := by
            rw [x.prop]
      have hsFixed : s • (x : X) ∈ F := by
        change
          (u : P) • (s • (x : X)) =
            s • (x : X)
        simpa only [sP, Subgroup.smul_def,
          Equiv.Perm.smul_def] using hfixP
      rw [← hs]
      exact hsFixed
    let orbitToFixed :
        MulAction.orbit S (x : X) → F :=
      fun y => ⟨y.1, horbitFixed y⟩
    have horbitToFixedInjective :
        Function.Injective orbitToFixed := by
      intro a b hab
      apply Subtype.ext
      have hab' :=
        congrArg (fun z : F => (z : X)) hab
      simpa only [orbitToFixed] using hab'
    have horbitLe :
      Fintype.card (MulAction.orbit S (x : X)) ≤
          Fintype.card F :=
      Fintype.card_le_of_injective
        orbitToFixed horbitToFixedInjective
    calc
      Nat.card S = Fintype.card S :=
        Nat.card_eq_fintype_card
      _ = Fintype.card
          (MulAction.orbit S (x : X)) :=
        horbit.symm
      _ ≤ Fintype.card F := horbitLe
      _ = 9 := hFcard
  have hnotTwentySeven : ¬27 ∣ Nat.card C := by
    intro htwentySeven
    have hpowDvd :
        3 ^ 3 ∣ Nat.card C := by
      exact htwentySeven
    have hpowDvdS :=
      S.pow_dvd_card_of_pow_dvd_card hpowDvd
    have hSpos : 0 < Nat.card S := Nat.card_pos
    have hTwentySevenLe : 27 ≤ Nat.card S :=
      Nat.le_of_dvd hSpos (by
        norm_num at hpowDvdS ⊢
        exact hpowDvdS)
    omega
  have hcoprimeFive :
      Nat.Coprime (Nat.card C) 5 :=
    ((show Nat.Prime 5 by norm_num).coprime_iff_not_dvd.mpr
      hnotFive).symm
  have hcoprimeSeven :
      Nat.Coprime (Nat.card C) 7 :=
    ((show Nat.Prime 7 by norm_num).coprime_iff_not_dvd.mpr
      hnotSeven).symm
  have hcoprimeThirtyFive :
      Nat.Coprime (Nat.card C) 35 := by
    rw [show 35 = 7 * 5 by norm_num]
    exact hcoprimeSeven.mul_right hcoprimeFive
  have hCdvdReduced : Nat.card C ∣ 114048 := by
    apply hcoprimeThirtyFive.dvd_of_dvd_mul_left
    norm_num at hCdiv ⊢
    exact hCdiv
  exact eleven_centralizer_arithmetic
    hCdvdReduced hnotTwentySeven

private theorem card_fixedBy_five_of_mem_eleven_conjugacy_orbit
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 20)
    (u : P) (huorder : orderOf u = 11)
    (a : MulAction.orbit (ConjAct P) u) :
    Fintype.card
      (MulAction.fixedBy (Fin 5 ↪ X) (a.1 : P)) = 15120 := by
  classical
  let g : Equiv.Perm X := u
  have hgorder : orderOf g = 11 := by
    calc
      orderOf g = orderOf u := Subgroup.orderOf_coe _
      _ = 11 := huorder
  have hgcycle : g.IsCycle :=
    Equiv.Perm.isCycle_of_prime_order' (by
      rw [hgorder]
      norm_num) (by
        rw [hcard, hgorder]
        norm_num)
  have hgsupport : g.support.card = 11 := by
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
      ((a.1 : P) : Equiv.Perm X).support.card = 11 := by
    calc
      ((a.1 : P) : Equiv.Perm X).support.card =
          (((q : P) : Equiv.Perm X) *
            ((a.1 : P) : Equiv.Perm X) *
            ((q : P) : Equiv.Perm X)⁻¹).support.card :=
        Equiv.Perm.card_support_conj.symm
      _ = g.support.card := by rw [hconjPerm]
      _ = 11 := hgsupport
  have hfixedX :
      Fintype.card
        (MulAction.fixedBy X (a.1 : P)) = 9 := by
    rw [Degree15.card_fixedBy_subgroup_perm, hcard,
      hasupport]
  calc
    Fintype.card
        (MulAction.fixedBy (Fin 5 ↪ X) (a.1 : P)) =
        (Fintype.card
          (MulAction.fixedBy X (a.1 : P))).descFactorial
            (Fintype.card (Fin 5)) :=
      Degree15.card_fixedBy_embedding (a.1 : P)
    _ = 15120 := by
      rw [hfixedX, Fintype.card_fin]
      norm_num [Nat.descFactorial]

theorem eleven_not_dvd_card_of_not_alternating
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 20)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P) :
    ¬11 ∣ Nat.card P := by
  classical
  intro h11
  letI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨u, huorder⟩ :=
    exists_prime_orderOf_dvd_card' 11 h11
  let C : Subgroup P :=
    Subgroup.centralizer ({u} : Set P)
  have hcentralizer : Nat.card C ≤ 12672 :=
    eleven_cycle_centralizer_card_le
      X P hcard h5 hnotAlt u huorder
  let A := MulAction.orbit (ConjAct P) u
  letI : Fintype A := Fintype.ofFinite _
  let val : A → P := fun a => a.1
  have hvalInjective : Function.Injective val :=
    Subtype.val_injective
  have hAcard :
      Fintype.card A * Nat.card C = Nat.card P := by
    letI :
        Fintype (MulAction.stabilizer (ConjAct P) u) :=
      Fintype.ofFinite _
    have hstabilizer :
        Fintype.card (MulAction.stabilizer (ConjAct P) u) =
          Nat.card C := by
      rw [← Nat.card_eq_fintype_card,
        ← Subgroup.nat_card_centralizer_nat_card_stabilizer]
    have horbitCard :=
      MulAction.card_orbit_mul_card_stabilizer_eq_card_group
        (ConjAct P) u
    rw [hstabilizer, ConjAct.card,
      ← Nat.card_eq_fintype_card] at horbitCard
    simpa [A, Nat.card_eq_fintype_card] using horbitCard
  have hfixed (a : A) :
      Fintype.card
          (MulAction.fixedBy (Fin 5 ↪ X) (val a)) = 15120 :=
    card_fixedBy_five_of_mem_eleven_conjugacy_orbit
      X P hcard u huorder a
  have hselectedSum :
      (∑ a : A,
          Fintype.card
            (MulAction.fixedBy (Fin 5 ↪ X) (val a))) =
        Fintype.card A * 15120 := by
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
  have hoverfill : Fintype.card A * 15120 ≤ Nat.card P := by
    calc
      Fintype.card A * 15120 =
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
  have hupper :
      Fintype.card A * Nat.card C ≤
        Fintype.card A * 12672 :=
    Nat.mul_le_mul_left _ hcentralizer
  omega

end FiveTransitive.Degree20

end CFSG
