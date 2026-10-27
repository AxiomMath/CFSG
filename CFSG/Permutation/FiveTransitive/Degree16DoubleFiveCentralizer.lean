module

public import CFSG.Permutation.FiveTransitive.ArithmeticChecks
public import CFSG.Permutation.FiveTransitive.Degree16SylowFive
public import CFSG.Permutation.FiveTransitive.Degree16

public section

namespace CFSG

namespace FiveTransitive.Degree16

open MulAction SubMulAction Subgroup

private abbrev DoubleFiveKernelDivisor :=
  ↥(Nat.divisors 3600)

private def doubleFiveKernelArithmeticPredicate
    (k : DoubleFiveKernelDivisor) : Prop :=
  ¬2 ∣ k.val →
    ¬3 ∣ k.val →
    k.val ≤ 25

private theorem double_five_kernel_arithmetic :
    ∀ k : DoubleFiveKernelDivisor,
      doubleFiveKernelArithmeticPredicate k := by
  intro k
  unfold doubleFiveKernelArithmeticPredicate
  exact FiveTransitive.ArithmeticChecks.le_twentyFive_of_dvd_3600 k.val
    (Nat.mem_divisors.mp k.property).1

theorem double_five_centralizer_card_le_fifty
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 16)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (hPcard : Nat.card P = 94348800)
    (S : Sylow 5 P) (hScard : Nat.card S = 25)
    (u : DoubleFiveElements X P S) :
    Nat.card
        (Subgroup.centralizer
          ({((u.1 : S) : P)} : Set P)) ≤ 50 := by
  classical
  let g : Equiv.Perm X := ((u.1 : S) : P)
  have huorder : orderOf u.1 = 5 :=
    sylow_five_nonidentity_order
      X P hcard S hScard u.2.1
  have hgorder : orderOf g = 5 := by
    calc
      orderOf g = orderOf ((u.1 : S) : P) :=
        Subgroup.orderOf_coe _
      _ = orderOf u.1 := Subgroup.orderOf_coe _
      _ = 5 := huorder
  have hgprime : (orderOf g).Prime := by
    rw [hgorder]
    norm_num
  obtain ⟨m, hm⟩ :=
    Equiv.Perm.cycleType_prime_order hgprime
  have hfixed :
      Fintype.card (MulAction.fixedBy X ((u.1 : S) : P)) = 6 :=
    u.2.2
  have hgsupport : g.support.card = 10 := by
    have h :=
      Degree15.card_fixedBy_subgroup_perm P ((u.1 : S) : P)
    change
      Fintype.card (MulAction.fixedBy X ((u.1 : S) : P)) =
        Fintype.card X - g.support.card at h
    rw [hfixed, hcard] at h
    omega
  have hsum := g.sum_cycleType
  rw [hm, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, hgorder, hgsupport] at hsum
  have hmTwo : m + 1 = 2 := by
    omega
  have hcycleType : g.cycleType = {5, 5} := by
    rw [hm, hgorder, hmTwo]
    norm_num
  let C : Subgroup P :=
    Subgroup.centralizer ({((u.1 : S) : P)} : Set P)
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
            ({g} : Set (Equiv.Perm X))) = 36000 := by
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
          (Equiv.Perm.OnCycleFactors.toPermHom g).ker = 18000 := by
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
      Nat.card cycleMap.ker ∣ 18000 := by
    rw [← hfullKerCard]
    exact Subgroup.card_dvd_of_injective kerMap hkerMapInjective
  have hkerDvdP :
      Nat.card cycleMap.ker ∣ 94348800 := by
    rw [← hPcard]
    exact (Subgroup.card_subgroup_dvd_card cycleMap.ker).trans
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
      have hcSupport : c.support.card = 5 := by
        have hmem : c.support.card ∈ ({5, 5} : Multiset ℕ) :=
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
    have hvSupportCard : vPerm.support.card ≤ 6 := by
      calc
        vPerm.support.card ≤ g.supportᶜ.card :=
          Finset.card_le_card hvSupport
        _ = 6 := by
          rw [Finset.card_compl, hcard, hgsupport]
    have hAlt :=
      alternatingGroup_le_of_prime_order_support_le_seven
        X P hcard h5 (vC : P).prop hq hvPermOrder (by
          change vPerm.support.card ≤ 7
          omega)
    exact hnotAlt hAlt
  have htwoNotDvd : ¬2 ∣ Nat.card cycleMap.ker :=
    hprimeNotDvd 2 (by norm_num) (Or.inl rfl)
  have hthreeNotDvd : ¬3 ∣ Nat.card cycleMap.ker :=
    hprimeNotDvd 3 (by norm_num) (Or.inr rfl)
  have hkerDvdGcd :
      Nat.card cycleMap.ker ∣
        Nat.gcd 18000 94348800 :=
    Nat.dvd_gcd hkerDvdFull hkerDvdP
  have hgcd : Nat.gcd 18000 94348800 = 3600 := by
    norm_num
  rw [hgcd] at hkerDvdGcd
  have hkerMem :
      Nat.card cycleMap.ker ∈ Nat.divisors 3600 :=
    Nat.mem_divisors.mpr
      ⟨hkerDvdGcd, by norm_num⟩
  let k : DoubleFiveKernelDivisor :=
    ⟨Nat.card cycleMap.ker, hkerMem⟩
  have hkerLe : Nat.card cycleMap.ker ≤ 25 := by
    exact double_five_kernel_arithmetic k
      htwoNotDvd hthreeNotDvd
  have hkerMul := cycleMap.ker.card_mul_index
  rw [Subgroup.index_ker] at hkerMul
  calc
    Nat.card C =
        Nat.card cycleMap.ker * Nat.card cycleMap.range :=
      hkerMul.symm
    _ ≤ 25 * 2 := Nat.mul_le_mul hkerLe hrangeLeTwo
    _ = 50 := by norm_num

theorem sylow_five_eq_of_double_five_mem
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 16)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (hPcard : Nat.card P = 94348800)
    (S T : Sylow 5 P) (hScard : Nat.card S = 25)
    (u : DoubleFiveElements X P S)
    (huT : ((u.1 : S) : P) ∈ T) :
    S = T := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hTcard : Nat.card T = 25 := by
    calc
      Nat.card T = Nat.card S :=
        Nat.card_congr (Sylow.equiv T S).toEquiv
      _ = 25 := hScard
  have hScomm : ∀ a b : S, a * b = b * a :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq
      (p := 5) (by
        calc
          Nat.card S = 25 := hScard
          _ = 5 ^ 2 := by norm_num)
      |>.is_comm.comm
  have hTcomm : ∀ a b : T, a * b = b * a :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq
      (p := 5) (by
        calc
          Nat.card T = 25 := hTcard
          _ = 5 ^ 2 := by norm_num)
      |>.is_comm.comm
  let uP : P := (u.1 : S)
  let C : Subgroup P :=
    Subgroup.centralizer ({uP} : Set P)
  have hSleC : (S : Subgroup P) ≤ C := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val
      (hScomm (⟨x, hx⟩ : S) u.1)
  have hTleC : (T : Subgroup P) ≤ C := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    let xT : T := ⟨x, hx⟩
    let uT : T := ⟨uP, huT⟩
    exact congrArg Subtype.val (hTcomm xT uT)
  let SC : Sylow 5 C := S.subtype hSleC
  let TC : Sylow 5 C := T.subtype hTleC
  have hSCcard : Nat.card SC = 25 := by
    calc
      Nat.card SC = Nat.card S :=
        Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe hSleC).toEquiv
      _ = 25 := hScard
  have hCcardLe : Nat.card C ≤ 50 := by
    simpa only [C, uP] using
      double_five_centralizer_card_le_fifty
        X P hcard h5 hnotAlt hPcard S hScard u
  have hSCindexMul := SC.index_mul_card
  rw [hSCcard] at hSCindexMul
  have hSCindexLe : SC.index ≤ 2 := by
    nlinarith
  have hSylowDvd : Nat.card (Sylow 5 C) ∣ SC.index :=
    SC.card_dvd_index
  have hSylowLe : Nat.card (Sylow 5 C) ≤ 2 :=
    (Nat.le_of_dvd
      (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      hSylowDvd).trans
      hSCindexLe
  have hSylowLeF : Fintype.card (Sylow 5 C) ≤ 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hSylowLe
  have hSylowMod := card_sylow_modEq_one 5 C
  have hSylowMod' : Fintype.card (Sylow 5 C) % 5 = 1 := by
    unfold Nat.ModEq at hSylowMod
    rw [Nat.card_eq_fintype_card] at hSylowMod
    norm_num at hSylowMod
    exact hSylowMod
  have hSylowCard : Fintype.card (Sylow 5 C) = 1 := by
    omega
  letI : Subsingleton (Sylow 5 C) :=
    Fintype.card_le_one_iff_subsingleton.mp (by omega)
  apply Sylow.subtype_injective (N := C)
  exact Subsingleton.elim SC TC

end FiveTransitive.Degree16

end CFSG
