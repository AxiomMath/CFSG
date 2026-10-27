module

public import CFSG.Permutation.FiveTransitive.Degree19FiveStabilizer

public section

namespace CFSG

namespace FiveTransitive.Degree19

open MulAction SubMulAction Subgroup

theorem nonidentity_sylow_fixed_embedding_bound
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    {p m f : ℕ} (hp : p.Prime)
    (S₀ : Sylow p P) (hS₀card : Nat.card S₀ = p)
    (hmCard : m ≤ Fintype.card X)
    (hfixed :
      ∀ a : Degree15.NonidentitySylowElements p P,
        Fintype.card
          (MulAction.fixedBy X
            (Degree15.nonidentitySylowElementVal p P a)) = f)
    (hm : MulAction.IsMultiplyPretransitive P X m) :
    let N := Subgroup.normalizer (S₀ : Set P)
    N.index * (p - 1) * f.descFactorial m ≤ Nat.card P := by
  classical
  dsimp
  letI : Fact p.Prime := ⟨hp⟩
  let A := Degree15.NonidentitySylowElements p P
  let val : A → P :=
    Degree15.nonidentitySylowElementVal p P
  let E := Fin m ↪ X
  have hfixedEmbedding (a : A) :
      Fintype.card (MulAction.fixedBy E (val a)) =
        f.descFactorial m := by
    calc
      Fintype.card (MulAction.fixedBy E (val a)) =
          (Fintype.card
            (MulAction.fixedBy X (val a))).descFactorial
              (Fintype.card (Fin m)) :=
        Degree15.card_fixedBy_embedding (val a)
      _ = f.descFactorial m := by
        rw [hfixed a, Fintype.card_fin]
  have hvalInjective : Function.Injective val :=
    Degree15.nonidentitySylowElementVal_injective
      S₀ hS₀card
  let N : Subgroup P :=
    Subgroup.normalizer (S₀ : Set P)
  have hAcard :
      Fintype.card A = N.index * (p - 1) := by
    rw [show Fintype.card A =
        Fintype.card (Sylow p P) * (p - 1) by
      exact Degree15.card_nonidentitySylowElements
        S₀ hS₀card]
    rw [← Nat.card_eq_fintype_card,
      S₀.card_eq_index_normalizer]
  have hselectedSum :
      (∑ a : A,
          Fintype.card (MulAction.fixedBy E (val a))) =
        N.index * (p - 1) * f.descFactorial m := by
    simp_rw [hfixedEmbedding]
    simp [hAcard]
  have hselectedLe :
      (∑ a : A,
          Fintype.card (MulAction.fixedBy E (val a))) ≤
        ∑ q : P,
          Fintype.card (MulAction.fixedBy E q) := by
    calc
      (∑ a : A,
          Fintype.card (MulAction.fixedBy E (val a))) =
          ∑ q ∈ Finset.univ.image val,
            Fintype.card (MulAction.fixedBy E q) := by
        rw [Finset.sum_image hvalInjective.injOn]
      _ ≤ ∑ q ∈ (Finset.univ : Finset P),
          Fintype.card (MulAction.fixedBy E q) :=
        Finset.sum_le_sum_of_subset (by simp)
      _ = ∑ q : P,
          Fintype.card (MulAction.fixedBy E q) := by
        simp
  letI : MulAction.IsPretransitive P E := by
    change MulAction.IsMultiplyPretransitive P X m
    exact hm
  letI : Nonempty E := Fintype.card_pos_iff.mp (by
    rw [Fintype.card_embedding_eq, Fintype.card_fin,
      Nat.descFactorial_pos]
    exact hmCard)
  letI : Unique (MulAction.orbitRel.Quotient P E) :=
    Classical.choice
      ((MulAction.pretransitive_iff_unique_quotient_of_nonempty
        P E).mp hm)
  have hburnside :=
    MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
      P E
  have hburnside' :
      (∑ q : P,
          Fintype.card (MulAction.fixedBy E q)) =
        Nat.card P := by
    rw [Fintype.card_unique, one_mul,
      ← Nat.card_eq_fintype_card] at hburnside
    exact hburnside
  calc
    N.index * (p - 1) * f.descFactorial m =
        ∑ a : A,
          Fintype.card (MulAction.fixedBy E (val a)) :=
      hselectedSum.symm
    _ ≤ ∑ q : P,
          Fintype.card (MulAction.fixedBy E q) :=
      hselectedLe
    _ = Nat.card P := hburnside'

theorem support_card_eq_fifteen_of_order_five_of_not_alternating
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 19)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (u : P) (huorder : orderOf u = 5) :
    (u : Equiv.Perm X).support.card = 15 := by
  classical
  let g : Equiv.Perm X := u
  have hgorder : orderOf g = 5 := by
    calc
      orderOf g = orderOf u := Subgroup.orderOf_coe _
      _ = 5 := huorder
  have hgprime : (orderOf g).Prime := by
    rw [hgorder]
    norm_num
  obtain ⟨k, hk⟩ :=
    Equiv.Perm.cycleType_prime_order hgprime
  have hsum := g.sum_cycleType
  rw [hk, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, hgorder] at hsum
  have hsupportLe : g.support.card ≤ 19 := by
    calc
      g.support.card ≤ Fintype.card X :=
        Finset.card_le_univ g.support
      _ = 19 := hcard
  have hkCases :
      k + 1 = 1 ∨ k + 1 = 2 ∨ k + 1 = 3 := by
    omega
  rcases hkCases with hkOne | hkTwo | hkThree
  · have hsupport : g.support.card = 5 := by
      omega
    exact (hnotAlt
      (Helpers.alternatingGroup_le_of_nontrivial_card_support_le_five
        X P h5 (by omega) u.prop (by
          intro hu
          have huP : u = 1 := Subtype.ext hu
          rw [huP, orderOf_one] at huorder
          norm_num at huorder) (by
            simpa only [g] using hsupport.le))).elim
  · have hsupport : g.support.card = 10 := by
      omega
    have hcentralizer :
        Nat.card
            (Subgroup.centralizer ({u} : Set P)) ≤ 4050 :=
      double_five_centralizer_card_le_four_thousand_fifty
        X P hcard h5 hnotAlt u huorder hsupport
    have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
      rw [MulAction.isMultiplyPretransitive_iff]
      intro a b
      obtain ⟨q, hq⟩ :=
        h5 a b a.injective b.injective
      refine ⟨q, ?_⟩
      ext i
      exact hq i
    exact (FiveTupleBurnside.conjugacy_orbit_overfills
      X P (by rw [hcard]; norm_num) hP5 u 15120
      (by omega)
      (card_fixedBy_five_of_mem_double_five_conjugacy_orbit
        X P hcard u hsupport)).elim
  · simpa only [g] using
      (show g.support.card = 15 by omega)

theorem sylow_five_card_eq_five
    (P : Type) [Group P] [Fintype P]
    (h : ℕ) (hPcard : Nat.card P = 1395360 * h)
    (hnotFive : ¬5 ∣ h)
    (S : Sylow 5 P) :
    Nat.card S = 5 := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hh : h ≠ 0 := by
    intro hz
    subst h
    exact hnotFive (dvd_zero 5)
  have hfactorization :
      (1395360 * h).factorization 5 = 1 := by
    rw [show 1395360 = 5 * 279072 by norm_num,
      Nat.mul_assoc,
      Nat.factorization_mul (by norm_num)
        (Nat.mul_ne_zero (by norm_num) hh),
      Finsupp.add_apply,
      (show Nat.Prime 5 by norm_num).factorization,
      Finsupp.single_eq_same,
      Nat.factorization_mul (by norm_num) hh,
      Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd hnotFive]
    norm_num
  rw [S.card_eq_multiplicity, hPcard,
    hfactorization]
  norm_num

private theorem card_le_five_of_dvd_125
    (k : ℕ) (hk : k ∣ 125) (h25 : ¬25 ∣ k) : k ≤ 5 := by
  have hpow : k ∣ 5 ^ 3 := hk
  obtain ⟨j, hj, rfl⟩ :=
    (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp hpow
  interval_cases j
  all_goals norm_num at h25
  all_goals norm_num

private theorem normalizer_card_arithmetic
    (n : ℕ) (hlower : 96 ≤ n) (hupper : n ≤ 120)
    (h20 : 20 ∣ n) (h25 : ¬25 ∣ n) : n = 120 := by omega

private theorem not_twenty_five_dvd_order
    (h : ℕ) (h5 : ¬5 ∣ h) : ¬25 ∣ 1395360 * h := by omega

private theorem triple_five_centralizer_card_le_thirty
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 19)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (h : ℕ) (hPcard : Nat.card P = 1395360 * h)
    (hnotFive : ¬5 ∣ h)
    (u : P) (huorder : orderOf u = 5)
    (husupport : (u : Equiv.Perm X).support.card = 15) :
    Nat.card
        (Subgroup.centralizer ({u} : Set P)) ≤ 30 := by
  classical
  let g : Equiv.Perm X := u
  have hgorder : orderOf g = 5 := by
    calc
      orderOf g = orderOf u := Subgroup.orderOf_coe _
      _ = 5 := huorder
  have hgprime : (orderOf g).Prime := by
    rw [hgorder]
    norm_num
  obtain ⟨k, hk⟩ :=
    Equiv.Perm.cycleType_prime_order hgprime
  have hsum := g.sum_cycleType
  rw [hk, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, hgorder, husupport] at hsum
  have hkThree : k + 1 = 3 := by
    omega
  have hcycleType : g.cycleType = {5, 5, 5} := by
    rw [hk, hgorder, hkThree]
    norm_num
  let C : Subgroup P :=
    Subgroup.centralizer ({u} : Set P)
  let baseMap : C →* Equiv.Perm X :=
    P.subtype.comp C.subtype
  have hbaseMapInjective : Function.Injective baseMap := by
    intro a b hab
    exact C.subtype_injective (P.subtype_injective hab)
  have hbaseMapMem :
      ∀ q : C, baseMap q ∈
        Subgroup.centralizer ({g} : Set (Equiv.Perm X)) := by
    intro q
    change ((q.1 : P) : Equiv.Perm X) ∈
      Subgroup.centralizer ({g} : Set (Equiv.Perm X))
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_singleton_iff.mp q.2)
  let centMap :
      C →* Subgroup.centralizer
        ({g} : Set (Equiv.Perm X)) :=
    baseMap.codRestrict
      (Subgroup.centralizer ({g} : Set (Equiv.Perm X)))
      hbaseMapMem
  have hcentMapInjective : Function.Injective centMap := by
    intro a b hab
    have hab' :=
      congrArg
        (fun x :
          Subgroup.centralizer
            ({g} : Set (Equiv.Perm X)) =>
          (x : Equiv.Perm X)) hab
    change baseMap a = baseMap b at hab'
    exact hbaseMapInjective hab'
  let cycleMap :
      C →* Equiv.Perm g.cycleFactorsFinset :=
    (Equiv.Perm.OnCycleFactors.toPermHom g).comp centMap
  have hcycleFactorCard :
      Fintype.card g.cycleFactorsFinset = 3 := by
    have h :=
      congrArg Multiset.card
        (Equiv.Perm.cycleType_def g)
    rw [hcycleType] at h
    simpa using h.symm
  have hcyclePermCard :
      Nat.card (Equiv.Perm g.cycleFactorsFinset) = 6 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card,
      hcycleFactorCard]
    norm_num
  have hrangeDvdSix : Nat.card cycleMap.range ∣ 6 := by
    rw [← hcyclePermCard]
    exact Subgroup.card_subgroup_dvd_card cycleMap.range
  have hrangeLeSix : Nat.card cycleMap.range ≤ 6 :=
    Nat.le_of_dvd (by norm_num) hrangeDvdSix
  have hfullCentralizer :
      Nat.card
          (Subgroup.centralizer
            ({g} : Set (Equiv.Perm X))) = 18000 := by
    rw [Equiv.Perm.nat_card_centralizer,
      hcycleType, hcard]
    norm_num
  have hfullRange :
      Nat.card
          (Equiv.Perm.OnCycleFactors.toPermHom g).range = 6 := by
    rw [Equiv.Perm.OnCycleFactors.nat_card_range_toPermHom,
      hcycleType]
    norm_num
  have hfullKerMul :=
    (Equiv.Perm.OnCycleFactors.toPermHom g).ker.card_mul_index
  rw [Subgroup.index_ker, hfullRange,
    hfullCentralizer] at hfullKerMul
  have hfullKerCard :
      Nat.card
          (Equiv.Perm.OnCycleFactors.toPermHom g).ker =
        3000 := by
    omega
  let kerMap :
      cycleMap.ker →*
        (Equiv.Perm.OnCycleFactors.toPermHom g).ker :=
    (centMap.comp cycleMap.ker.subtype).codRestrict
      (Equiv.Perm.OnCycleFactors.toPermHom g).ker (by
        intro q
        exact q.2)
  have hkerMapInjective : Function.Injective kerMap := by
    intro a b hab
    have hab' := congrArg Subtype.val hab
    change centMap a.1 = centMap b.1 at hab'
    exact Subtype.ext (hcentMapInjective hab')
  have hkerDvdFull :
      Nat.card cycleMap.ker ∣ 3000 := by
    rw [← hfullKerCard]
    exact Subgroup.card_dvd_of_injective
      kerMap hkerMapInjective
  have hkerDvdP :
      Nat.card cycleMap.ker ∣ Nat.card P :=
    (Subgroup.card_subgroup_dvd_card cycleMap.ker).trans
      (Subgroup.card_subgroup_dvd_card C)
  have hprimeNotDvd :
      ∀ q : ℕ, q.Prime → (q = 2 ∨ q = 3) →
        ¬q ∣ Nat.card cycleMap.ker := by
    intro q hq hqCases hqdvd
    letI : Fact q.Prime := ⟨hq⟩
    obtain ⟨v, hvorder⟩ :=
      exists_prime_orderOf_dvd_card'
        (G := cycleMap.ker) q hqdvd
    let vC : C := v
    let vPerm : Equiv.Perm X := baseMap vC
    have hvPermOrder : orderOf vPerm = q := by
      calc
        orderOf vPerm = orderOf vC :=
          orderOf_injective baseMap
            hbaseMapInjective vC
        _ = orderOf v := Subgroup.orderOf_coe _
        _ = q := hvorder
    have hvKer :
        centMap vC ∈
          (Equiv.Perm.OnCycleFactors.toPermHom g).ker := by
      change
        (Equiv.Perm.OnCycleFactors.toPermHom g)
            (centMap vC) = 1
      exact v.prop
    have hvCommutes :
        ∀ c ∈ g.cycleFactorsFinset,
          Commute vPerm c := by
      have hcommutes :=
        (Equiv.Perm.OnCycleFactors.mem_ker_toPermHom_iff
          (g := g) (centMap vC)).mp hvKer
      intro c hc
      have hcomm := hcommutes c hc
      change Commute (baseMap vC) c at hcomm
      exact hcomm
    have hvSupport :
        vPerm.support ⊆ g.supportᶜ := by
      intro x hx
      rw [Finset.mem_compl]
      intro hxg
      obtain ⟨c, hc, hxc⟩ :=
        Equiv.Perm.mem_support_iff_mem_support_of_mem_cycleFactorsFinset.mp
          hxg
      have hcCycle : c.IsCycle :=
        (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hc).1
      have hcTypeLe :=
        Equiv.Perm.cycleType_le_of_mem_cycleFactorsFinset hc
      rw [hcCycle.cycleType, hcycleType] at hcTypeLe
      have hcSupport : c.support.card = 5 := by
        have hmem :
            c.support.card ∈
              ({5, 5, 5} : Multiset ℕ) :=
          Multiset.mem_of_le hcTypeLe (by simp)
        simpa using hmem
      have hcOrder : orderOf c = 5 := by
        rw [hcCycle.orderOf, hcSupport]
      have hcoprime :
          Nat.Coprime (orderOf vPerm) (orderOf c) := by
        rw [hvPermOrder, hcOrder]
        rcases hqCases with rfl | rfl <;> norm_num
      have houtside :=
        PermCentralizer.support_le_compl_of_isCycle_of_commute_of_coprime_order
          hcCycle (hvCommutes c hc) hcoprime hx
      exact (Finset.mem_compl.mp houtside) hxc
    have hvSupportCard : vPerm.support.card ≤ 4 := by
      calc
        vPerm.support.card ≤ g.supportᶜ.card :=
          Finset.card_le_card hvSupport
        _ = 4 := by
          rw [Finset.card_compl, hcard, husupport]
    have hvNe : vPerm ≠ 1 := by
      intro hv
      rw [hv, orderOf_one] at hvPermOrder
      exact hq.ne_one hvPermOrder.symm
    exact hnotAlt
      (alternatingGroup_le_of_nontrivial_support_le_seven
        X P hcard h5 (vC : P).prop hvNe (by
          change vPerm.support.card ≤ 7
          omega))
  have htwoNotDvd : ¬2 ∣ Nat.card cycleMap.ker :=
    hprimeNotDvd 2 (by norm_num) (Or.inl rfl)
  have hthreeNotDvd : ¬3 ∣ Nat.card cycleMap.ker :=
    hprimeNotDvd 3 (by norm_num) (Or.inr rfl)
  have hcoprimeEight :
      Nat.Coprime (Nat.card cycleMap.ker) (2 ^ 3) :=
    Nat.prime_two.coprime_pow_of_not_dvd htwoNotDvd
  have hcoprimeThree :
      Nat.Coprime (Nat.card cycleMap.ker) 3 :=
    (Nat.prime_three.coprime_iff_not_dvd.mpr
      hthreeNotDvd).symm
  have hcoprimeTwentyFour :
      Nat.Coprime (Nat.card cycleMap.ker) 24 := by
    rw [show 24 = 3 * 2 ^ 3 by norm_num]
    exact hcoprimeThree.mul_right hcoprimeEight
  have hkerDvdOneTwentyFive :
      Nat.card cycleMap.ker ∣ 125 := by
    apply hcoprimeTwentyFour.dvd_of_dvd_mul_left
    norm_num at hkerDvdFull ⊢
    exact hkerDvdFull
  have hh : h ≠ 0 := by
    intro hz
    subst h
    exact hnotFive (dvd_zero 5)
  have hnotTwentyFiveP : ¬25 ∣ Nat.card P := by
    rw [hPcard]
    exact not_twenty_five_dvd_order h hnotFive
  have hnotTwentyFiveKer :
      ¬25 ∣ Nat.card cycleMap.ker :=
    fun hdvd => hnotTwentyFiveP (hdvd.trans hkerDvdP)
  have hkerLeFive : Nat.card cycleMap.ker ≤ 5 :=
    card_le_five_of_dvd_125 _ hkerDvdOneTwentyFive hnotTwentyFiveKer
  have hkerMul := cycleMap.ker.card_mul_index
  rw [Subgroup.index_ker] at hkerMul
  calc
    Nat.card C =
        Nat.card cycleMap.ker * Nat.card cycleMap.range :=
      hkerMul.symm
    _ ≤ 5 * 6 :=
      Nat.mul_le_mul hkerLeFive hrangeLeSix
    _ = 30 := by norm_num

theorem sylow_five_normalizer_card_eq_one_twenty
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 19)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 5 P) :
    Nat.card (Subgroup.normalizer (S : Set P)) = 120 ∧
      (3 * Nat.card (fixingSubgroup P s)) % 5 = 1 := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  let h := Nat.card H
  have hnotFive : ¬5 ∣ h :=
    five_not_dvd_five_point_stabilizer_of_not_alternating
      X P hcard h5 hnotAlt s hs
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      h5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact hq i
  have hfixIndex := hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hfixIndex
  norm_num at hfixIndex
  have hHindex : H.index = 1395360 := by
    change (fixingSubgroup P s).index = 1395360
    omega
  have hHindexCard := H.index_mul_card
  have hPcard : Nat.card P = 1395360 * h := by
    rw [hHindex] at hHindexCard
    exact hHindexCard.symm
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hScard : Nat.card S = 5 :=
    sylow_five_card_eq_five P h hPcard hnotFive S
  let N : Subgroup P :=
    Subgroup.normalizer (S : Set P)
  have hfixed
      (a : Degree15.NonidentitySylowElements 5 P) :
      Fintype.card
          (MulAction.fixedBy X
            (Degree15.nonidentitySylowElementVal 5 P a)) = 4 := by
    rcases a with ⟨T, u⟩
    change
      Fintype.card
          (MulAction.fixedBy X ((u.1 : T) : P)) = 4
    have hTcard : Nat.card T = 5 :=
      Degree15.sylow_card_eq_of_card_eq S hScard T
    have huorderT : orderOf u.1 = 5 :=
      Degree15.orderOf_eq_prime_of_card_eq_prime
        hTcard u.2
    have huorder :
        orderOf ((u.1 : T) : P) = 5 := by
      calc
        orderOf ((u.1 : T) : P) =
            orderOf u.1 := Subgroup.orderOf_coe _
        _ = 5 := huorderT
    have husupport :
        ((((u.1 : T) : P) : Equiv.Perm X)).support.card =
          15 :=
      support_card_eq_fifteen_of_order_five_of_not_alternating
        X P hcard h5 hnotAlt ((u.1 : T) : P) huorder
    rw [Degree15.card_fixedBy_subgroup_perm, hcard,
      husupport]
  have hP4 : MulAction.IsMultiplyPretransitive P X 4 := by
    letI : MulAction.IsMultiplyPretransitive P X 5 := hP5
    exact MulAction.isMultiplyPretransitive_of_le
      (G := P) (α := X) (m := 4) (n := 5)
        (by omega) (by
          rw [Nat.card_eq_fintype_card, hcard]
          omega)
  have hfixedBound :
      N.index * (5 - 1) *
          (4 : ℕ).descFactorial 4 ≤
        Nat.card P := by
    simpa only [N] using
      nonidentity_sylow_fixed_embedding_bound
        X P (p := 5) (m := 4) (f := 4)
          (by norm_num) S hScard (by omega)
          hfixed hP4
  have hfixedBoundNat :
      N.index * 96 ≤ Nat.card P := by
    norm_num [Nat.descFactorial] at hfixedBound
    rw [Nat.card_eq_fintype_card]
    nlinarith
  have hNcardLower : 96 ≤ Nat.card N := by
    have hscaled :
        N.index * 96 ≤ N.index * Nat.card N := by
      rw [N.index_mul_card]
      exact hfixedBoundNat
    exact Nat.le_of_mul_le_mul_left hscaled
      (Nat.pos_of_ne_zero
        Subgroup.index_ne_zero_of_finite)
  letI : IsCyclic S :=
    isCyclic_of_prime_card hScard
  letI : IsMulCommutative S :=
    IsCyclic.isMulCommutative
  obtain ⟨u, huorder⟩ :=
    IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have huorderS : orderOf u = 5 :=
    huorder.trans hScard
  have huorderP : orderOf (u : P) = 5 := by
    calc
      orderOf (u : P) = orderOf u :=
        Subgroup.orderOf_coe _
      _ = 5 := huorderS
  have husupport :
      (((u : S) : P) : Equiv.Perm X).support.card =
        15 :=
    support_card_eq_fifteen_of_order_five_of_not_alternating
      X P hcard h5 hnotAlt (u : P) huorderP
  let C : Subgroup P :=
    Subgroup.centralizer (S : Set P)
  have hSleC : (S : Subgroup P) ≤ C := by
    intro a ha b hb
    exact congrArg Subtype.val
      (mul_comm'
        (⟨b, hb⟩ : S) (⟨a, ha⟩ : S))
  have hCle :
      C ≤ Subgroup.centralizer
        ({(u : P)} : Set P) := by
    intro q hq
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hq (u : P) u.prop).symm
  have hCcardLe : Nat.card C ≤ 30 := by
    have hdiv := Subgroup.card_dvd_of_le hCle
    exact (Nat.le_of_dvd Nat.card_pos hdiv).trans
      (triple_five_centralizer_card_le_thirty
        X P hcard h5 hnotAlt h hPcard hnotFive
          (u : P) huorderP husupport)
  have hAutCard : Nat.card (MulAut S) = 4 := by
    rw [IsCyclic.card_mulAut S, hScard,
      Nat.totient_prime (by norm_num)]
  have hrangeDvd :
      Nat.card S.normalizerMonoidHom.range ∣ 4 := by
    rw [← hAutCard]
    exact Subgroup.card_subgroup_dvd_card _
  have hrEq :
      C.relIndex N =
        Nat.card S.normalizerMonoidHom.range := by
    change
      (Subgroup.centralizer (S : Set P)).relIndex
          (Subgroup.normalizer (S : Set P)) =
        Nat.card S.normalizerMonoidHom.range
    rw [Subgroup.relIndex, ← Subgroup.index_ker,
      S.normalizerMonoidHom_ker]
    simp only [S.coe_coe]
  have hrDvd : C.relIndex N ∣ 4 := by
    rwa [hrEq]
  letI : C.IsFiniteRelIndex N :=
    Subgroup.isFiniteRelIndex_of_finiteIndex
  have hrPos : 0 < C.relIndex N :=
    Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero
  have hrel :
      C.relIndex N * N.index = C.index :=
    Subgroup.relIndex_mul_index
      (Subgroup.centralizer_le_normalizer (S : Set P))
  have hNcardEq :
      Nat.card N = C.relIndex N * Nat.card C := by
    have hprod :
        N.index * (C.relIndex N * Nat.card C) =
          N.index * Nat.card N := by
      calc
        N.index * (C.relIndex N * Nat.card C) =
            C.index * Nat.card C := by
          rw [← hrel]
          ac_rfl
        _ = Nat.card P := C.index_mul_card
        _ = N.index * Nat.card N :=
          N.index_mul_card.symm
    exact (Nat.mul_left_cancel
      (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      hprod).symm
  have hrFour : C.relIndex N = 4 := by
    have hrLe : C.relIndex N ≤ 4 :=
      Nat.le_of_dvd (by norm_num) hrDvd
    interval_cases C.relIndex N
    all_goals try norm_num at hrDvd
    all_goals omega
  have hfourDvd : 4 ∣ Nat.card N := by
    rw [hNcardEq, hrFour]
    exact Nat.dvd_mul_right 4 (Nat.card C)
  have hfiveDvd : 5 ∣ Nat.card N := by
    rw [← hScard]
    exact Subgroup.card_dvd_of_le
      (hSleC.trans
        (Subgroup.centralizer_le_normalizer
          (S : Set P)))
  have htwentyDvd : 20 ∣ Nat.card N := by
    simpa using Nat.Coprime.mul_dvd_of_dvd_of_dvd
      (by norm_num : Nat.Coprime 4 5)
        hfourDvd hfiveDvd
  have hNcardLe : Nat.card N ≤ 120 := by
    rw [hNcardEq]
    exact (Nat.mul_le_mul
      (Nat.le_of_dvd (by norm_num) hrDvd)
      hCcardLe).trans (by norm_num)
  have hh : h ≠ 0 :=
    Nat.card_pos.ne'
  have hnotTwentyFiveP : ¬25 ∣ Nat.card P := by
    rw [hPcard]
    exact not_twenty_five_dvd_order h hnotFive
  have hNcardDvdP : Nat.card N ∣ Nat.card P :=
    Subgroup.card_subgroup_dvd_card N
  have hnotTwentyFiveN : ¬25 ∣ Nat.card N :=
    fun hdvd =>
      hnotTwentyFiveP (hdvd.trans hNcardDvdP)
  have hNcard : Nat.card N = 120 :=
    normalizer_card_arithmetic _ hNcardLower hNcardLe htwentyDvd hnotTwentyFiveN
  have hsmod : N.index % 5 = 1 := by
    have hsylow : N.index ≡ 1 [MOD 5] := by
      change
        (Subgroup.normalizer (S : Set P)).index ≡
          1 [MOD 5]
      rw [← S.card_eq_index_normalizer]
      exact card_sylow_modEq_one 5 P
    change N.index % 5 = 1 % 5 at hsylow
    norm_num at hsylow
    exact hsylow
  have hNindexCard := N.index_mul_card
  have hNindex :
      N.index = 11628 * h := by
    rw [hNcard, hPcard] at hNindexCard
    omega
  refine ⟨hNcard, ?_⟩
  rw [hNindex] at hsmod
  change (3 * h) % 5 = 1
  simpa [Nat.mul_mod] using hsmod

end FiveTransitive.Degree19

end CFSG
