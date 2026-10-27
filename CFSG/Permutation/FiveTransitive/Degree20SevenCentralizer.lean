module

public import CFSG.Permutation.FiveTransitive.ArithmeticChecks
public import CFSG.Permutation.FiveTransitive.Degree20SmallSupport
public import CFSG.Permutation.FiveTransitive.Degree15FixedPoint

public section

namespace CFSG

namespace FiveTransitive.Degree20

open MulAction SubMulAction Subgroup

private abbrev DoubleSevenKernelDivisor :=
  ↥(Nat.divisors 35280)

private def doubleSevenKernelArithmeticPredicate
    (k : DoubleSevenKernelDivisor) : Prop :=
  ¬2 ∣ k.val →
    ¬3 ∣ k.val →
    ¬5 ∣ k.val →
    ¬49 ∣ k.val →
    k.val ≤ 7

private theorem double_seven_kernel_arithmetic :
    ∀ k : DoubleSevenKernelDivisor,
      doubleSevenKernelArithmeticPredicate k := by
  intro k h2 h3 h5 h49
  exact ArithmeticChecks.le_seven_of_dvd_35280 k.val
    (Nat.dvd_of_mem_divisors k.prop) h2 h3 h5 h49

theorem sylowSeven_element_centralizer_card_le_fourteen
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 20)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (S : Sylow 7 P) (hScard : Nat.card S = 7)
    (u : S) (hu : u ≠ 1) :
    Nat.card
        (Subgroup.centralizer ({(u : P)} : Set P)) ≤ 14 := by
  classical
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have huorder : orderOf u = 7 :=
    Degree15.orderOf_eq_prime_of_card_eq_prime hScard hu
  let g : Equiv.Perm X := (u : P)
  have hgorder : orderOf g = 7 := by
    calc
      orderOf g = orderOf (u : P) := Subgroup.orderOf_coe _
      _ = orderOf u := Subgroup.orderOf_coe _
      _ = 7 := huorder
  have hgprime : (orderOf g).Prime := by
    rw [hgorder]
    norm_num
  obtain ⟨m, hm⟩ :=
    Equiv.Perm.cycleType_prime_order hgprime
  have hsum := g.sum_cycleType
  rw [hm, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, hgorder] at hsum
  have hsupportLe : g.support.card ≤ 20 := by
    calc
      g.support.card ≤ Fintype.card X :=
        Finset.card_le_univ g.support
      _ = 20 := hcard
  have hmTwo : m + 1 = 2 := by
    have hmLe : m + 1 ≤ 2 := by
      nlinarith
    rcases (show m + 1 = 1 ∨ m + 1 = 2 by omega) with hmOne | hmTwo
    · have hgcycle : g.IsCycle := by
        rw [← Equiv.Perm.card_cycleType_eq_one, hm, hmOne]
        simp
      have hgsupport : g.support.card = 7 := by
        omega
      exact (hnotAlt
        (Degree20Seven.alternatingGroup_le_of_sevenCycle
          X P hcard h5 (u : P).prop hgcycle hgsupport)).elim
    · exact hmTwo
  have hcycleType : g.cycleType = {7, 7} := by
    rw [hm, hgorder, hmTwo]
    norm_num
  have hgsupport : g.support.card = 14 := by
    rw [← g.sum_cycleType, hcycleType]
    norm_num
  let C : Subgroup P :=
    Subgroup.centralizer ({(u : P)} : Set P)
  let baseMap : C →* Equiv.Perm X :=
    P.subtype.comp C.subtype
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
      C →* Subgroup.centralizer ({g} : Set (Equiv.Perm X)) :=
    baseMap.codRestrict
      (Subgroup.centralizer ({g} : Set (Equiv.Perm X)))
      hbaseMapMem
  have hcentMapInjective : Function.Injective centMap := by
    intro a b hab
    have hab' := congrArg Subtype.val hab
    change baseMap a = baseMap b at hab'
    exact C.subtype_injective (P.subtype_injective hab')
  let cycleMap :
      C →* Equiv.Perm g.cycleFactorsFinset :=
    (Equiv.Perm.OnCycleFactors.toPermHom g).comp centMap
  have hcycleFactorCard :
      Fintype.card g.cycleFactorsFinset = 2 := by
    have h :=
      congrArg Multiset.card
        (Equiv.Perm.cycleType_def g)
    rw [hcycleType] at h
    simpa using h.symm
  have hcyclePermCard :
      Nat.card (Equiv.Perm g.cycleFactorsFinset) = 2 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card,
      hcycleFactorCard]
    norm_num
  have hrangeDvdTwo : Nat.card cycleMap.range ∣ 2 := by
    rw [← hcyclePermCard]
    exact Subgroup.card_subgroup_dvd_card cycleMap.range
  have hrangeLeTwo : Nat.card cycleMap.range ≤ 2 :=
    Nat.le_of_dvd (by norm_num) hrangeDvdTwo
  have hfullCentralizer :
      Nat.card
          (Subgroup.centralizer
            ({g} : Set (Equiv.Perm X))) = 70560 := by
    rw [Equiv.Perm.nat_card_centralizer, hcycleType, hcard]
    norm_num
  have hfullRange :
      Nat.card
          (Equiv.Perm.OnCycleFactors.toPermHom g).range = 2 := by
    rw [Equiv.Perm.OnCycleFactors.nat_card_range_toPermHom,
      hcycleType]
    norm_num
  have hfullKerMul :=
    (Equiv.Perm.OnCycleFactors.toPermHom g).ker.card_mul_index
  rw [Subgroup.index_ker, hfullRange,
    hfullCentralizer] at hfullKerMul
  have hfullKerCard :
      Nat.card
          (Equiv.Perm.OnCycleFactors.toPermHom g).ker = 35280 := by
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
      Nat.card cycleMap.ker ∣ 35280 := by
    rw [← hfullKerCard]
    exact Subgroup.card_dvd_of_injective kerMap hkerMapInjective
  have hkerDvdP :
      Nat.card cycleMap.ker ∣ Nat.card P :=
    (Subgroup.card_subgroup_dvd_card cycleMap.ker).trans
      (Subgroup.card_subgroup_dvd_card C)
  have hprimeNotDvd :
      ∀ q : ℕ, q.Prime → (q = 2 ∨ q = 3 ∨ q = 5) →
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
            (fun _ _ h => C.subtype_injective
              (P.subtype_injective h)) vC
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
      have h :=
        (Equiv.Perm.OnCycleFactors.mem_ker_toPermHom_iff
          (g := g) (centMap vC)).mp hvKer
      intro c hc
      have hcomm := h c hc
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
      have hcSupport : c.support.card = 7 := by
        have hmem : c.support.card ∈ ({7, 7} : Multiset ℕ) :=
          Multiset.mem_of_le hcTypeLe (by simp)
        simpa using hmem
      have hcOrder : orderOf c = 7 := by
        rw [hcCycle.orderOf, hcSupport]
      have hcoprime :
          Nat.Coprime (orderOf vPerm) (orderOf c) := by
        rw [hvPermOrder, hcOrder]
        rcases hqCases with rfl | rfl | rfl <;> norm_num
      have houtside :=
        PermCentralizer.support_le_compl_of_isCycle_of_commute_of_coprime_order
          hcCycle (hvCommutes c hc) hcoprime hx
      exact (Finset.mem_compl.mp houtside) hxc
    have hvSupportCard : vPerm.support.card ≤ 6 := by
      calc
        vPerm.support.card ≤ g.supportᶜ.card :=
          Finset.card_le_card hvSupport
        _ = 6 := by
          rw [Finset.card_compl, hcard, hgsupport]
    have hvNe : vPerm ≠ 1 := by
      intro hv
      have : orderOf vPerm = 1 :=
        orderOf_eq_one_iff.mpr hv
      rw [hvPermOrder] at this
      exact hq.ne_one this
    have hvSupportCard' :
        (((vC : P) : Equiv.Perm X)).support.card ≤ 7 := by
      change vPerm.support.card ≤ 7
      omega
    exact hnotAlt
      (alternatingGroup_le_of_nontrivial_support_le_seven
        X P hcard h5 (vC : P).prop hvNe hvSupportCard')
  have htwoNotDvd : ¬2 ∣ Nat.card cycleMap.ker :=
    hprimeNotDvd 2 (by norm_num) (Or.inl rfl)
  have hthreeNotDvd : ¬3 ∣ Nat.card cycleMap.ker :=
    hprimeNotDvd 3 (by norm_num) (Or.inr (Or.inl rfl))
  have hfiveNotDvd : ¬5 ∣ Nat.card cycleMap.ker :=
    hprimeNotDvd 5 (by norm_num) (Or.inr (Or.inr rfl))
  have hfortyNineNotDvd : ¬49 ∣ Nat.card cycleMap.ker := by
    intro hfortyNine
    have hfortyNineP : 49 ∣ Nat.card P :=
      hfortyNine.trans hkerDvdP
    have hpowDvd : 7 ^ 2 ∣ Nat.card P := by
      change 49 ∣ Nat.card P
      exact hfortyNineP
    have hpowDvdS := S.pow_dvd_card_of_pow_dvd_card hpowDvd
    rw [hScard] at hpowDvdS
    norm_num at hpowDvdS
  have hkerMem :
      Nat.card cycleMap.ker ∈ Nat.divisors 35280 :=
    Nat.mem_divisors.mpr
      ⟨hkerDvdFull, by norm_num⟩
  let k : DoubleSevenKernelDivisor :=
    ⟨Nat.card cycleMap.ker, hkerMem⟩
  have hkerLe : Nat.card cycleMap.ker ≤ 7 :=
    double_seven_kernel_arithmetic k
      htwoNotDvd hthreeNotDvd hfiveNotDvd hfortyNineNotDvd
  have hkerMul := cycleMap.ker.card_mul_index
  rw [Subgroup.index_ker] at hkerMul
  calc
    Nat.card C =
        Nat.card cycleMap.ker * Nat.card cycleMap.range :=
      hkerMul.symm
    _ ≤ 7 * 2 := Nat.mul_le_mul hkerLe hrangeLeTwo
    _ = 14 := by norm_num

end FiveTransitive.Degree20

end CFSG
