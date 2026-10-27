module

public import CFSG.Permutation.FiveTransitive.Degree19SmallSupport
public import CFSG.Permutation.FiveTransitive.PermCentralizer

public section

namespace CFSG

namespace FiveTransitive.Degree19

open MulAction SubMulAction Subgroup

@[expose] def centralizerToFixedPoints
    {X : Type} [Fintype X] [DecidableEq X]
    (g : Equiv.Perm X) :
    Subgroup.centralizer ({g} : Set (Equiv.Perm X)) →*
      Equiv.Perm (Function.fixedPoints g) where
  toFun p :=
    p.1.subtypePerm
      (fun x =>
        Equiv.Perm.apply_mem_fixedPoints_iff_mem_of_mem_centralizer
          p.2)
  map_one' := by
    ext x
    rfl
  map_mul' a b := by
    ext x
    rfl

@[expose] def centralizerToSupport
    {X : Type} [Fintype X] [DecidableEq X]
    (g : Equiv.Perm X) :
    Subgroup.centralizer ({g} : Set (Equiv.Perm X)) →*
      Equiv.Perm g.support where
  toFun p :=
    p.1.subtypePerm
      (fun x =>
        Equiv.Perm.mem_support_iff_of_commute
          (Subgroup.mem_centralizer_singleton_iff.mp p.2) x)
  map_one' := by
    ext x
    rfl
  map_mul' a b := by
    ext x
    rfl

private theorem dvd_one_twenty_five_of_dvd_double_five_kernel
    {k : ℕ} (hkdvd : k ∣ 9072000)
    (htwo : ¬2 ∣ k) (hthree : ¬3 ∣ k)
    (hseven : ¬7 ∣ k) :
    k ∣ 125 := by
  have hcoprimeTwo : Nat.Coprime k (2 ^ 7) :=
    Nat.prime_two.coprime_pow_of_not_dvd htwo
  have hcoprimeThree : Nat.Coprime k (3 ^ 4) :=
    Nat.prime_three.coprime_pow_of_not_dvd hthree
  have hcoprimeSeven : Nat.Coprime k 7 :=
    ((show Nat.Prime 7 by norm_num).coprime_iff_not_dvd.mpr
      hseven).symm
  have hcoprime :
      Nat.Coprime k (7 * (3 ^ 4 * 2 ^ 7)) :=
    hcoprimeSeven.mul_right
      (hcoprimeThree.mul_right hcoprimeTwo)
  apply hcoprime.dvd_of_dvd_mul_left
  norm_num at hkdvd ⊢
  exact hkdvd

private theorem le_twenty_five_of_dvd_one_twenty_five
    {k : ℕ} (hkdvd : k ∣ 125) (hne : k ≠ 125) :
    k ≤ 25 := by
  have hkdvd' : k ∣ 5 ^ 3 := by
    norm_num
    exact hkdvd
  obtain ⟨j, hj, hkj⟩ :=
    (Nat.dvd_prime_pow (by norm_num)).mp hkdvd'
  rw [hkj] at hne ⊢
  interval_cases j <;> norm_num at *

theorem double_five_centralizer_card_le_four_thousand_fifty
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 19)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (u : P) (huorder : orderOf u = 5)
    (husupport : (u : Equiv.Perm X).support.card = 10) :
    Nat.card
        (Subgroup.centralizer ({u} : Set P)) ≤ 4050 := by
  classical
  let g : Equiv.Perm X := u
  have hgorder : orderOf g = 5 := by
    calc
      orderOf g = orderOf u := Subgroup.orderOf_coe _
      _ = 5 := huorder
  have hgprime : (orderOf g).Prime := by
    rw [hgorder]
    norm_num
  obtain ⟨n, hn⟩ :=
    Equiv.Perm.cycleType_prime_order hgprime
  have hsum := g.sum_cycleType
  rw [hn, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, hgorder, husupport] at hsum
  have hnTwo : n + 1 = 2 := by
    omega
  have hcycleType : g.cycleType = {5, 5} := by
    rw [hn, hgorder, hnTwo]
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
            ({g} : Set (Equiv.Perm X))) = 18144000 := by
    rw [Equiv.Perm.nat_card_centralizer,
      hcycleType, hcard]
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
          (Equiv.Perm.OnCycleFactors.toPermHom g).ker =
        9072000 := by
    omega
  let K : Subgroup C := cycleMap.ker
  let kerMap :
      K →*
        (Equiv.Perm.OnCycleFactors.toPermHom g).ker :=
    (centMap.comp K.subtype).codRestrict
      (Equiv.Perm.OnCycleFactors.toPermHom g).ker (by
        intro q
        exact q.2)
  have hkerMapInjective : Function.Injective kerMap := by
    intro a b hab
    have hab' := congrArg Subtype.val hab
    change centMap a.1 = centMap b.1 at hab'
    exact Subtype.ext (hcentMapInjective hab')
  have hKDvdFull : Nat.card K ∣ 9072000 := by
    rw [← hfullKerCard]
    exact Subgroup.card_dvd_of_injective
      kerMap hkerMapInjective
  let fixedMap :
      K →* Equiv.Perm (Function.fixedPoints g) :=
    (centralizerToFixedPoints g).comp
      (centMap.comp K.subtype)
  let F := Function.fixedPoints g
  have hFcard : Nat.card F = 9 := by
    rw [Nat.card_eq_fintype_card,
      Equiv.Perm.card_fixedPoints, hcycleType, hcard]
    norm_num
  letI : MulAction K F :=
    MulAction.compHom F fixedMap
  letI : Nontrivial F :=
    Fintype.one_lt_card_iff_nontrivial.mp (by
      rw [← Nat.card_eq_fintype_card, hFcard]
      norm_num)
  obtain ⟨y, z, hyz⟩ := exists_pair_ne F
  let L : Subgroup K :=
    MulAction.stabilizer K y
  let M : Subgroup L :=
    MulAction.stabilizer L z
  have hLindexOrbit :
      L.index = (MulAction.orbit K y).ncard := by
    simpa only [L] using MulAction.index_stabilizer K y
  have hLindexLe : L.index ≤ 9 := by
    calc
      L.index = (MulAction.orbit K y).ncard :=
        hLindexOrbit
      _ ≤ (Set.univ : Set F).ncard :=
        Set.ncard_le_ncard (Set.subset_univ _)
      _ = Nat.card F := Set.ncard_univ F
      _ = 9 := hFcard
  have hMindexOrbit :
      M.index = (MulAction.orbit L z).ncard := by
    simpa only [M] using MulAction.index_stabilizer L z
  have hMindexLe : M.index ≤ 9 := by
    calc
      M.index = (MulAction.orbit L z).ncard :=
        hMindexOrbit
      _ ≤ (Set.univ : Set F).ncard :=
        Set.ncard_le_ncard (Set.subset_univ _)
      _ = Nat.card F := Set.ncard_univ F
      _ = 9 := hFcard
  let mToK : M →* K :=
    L.subtype.comp M.subtype
  let mToC : M →* C :=
    K.subtype.comp mToK
  let mCentMap :
      M →* Subgroup.centralizer
        ({g} : Set (Equiv.Perm X)) :=
    centMap.comp mToC
  let mBaseMap : M →* Equiv.Perm X :=
    baseMap.comp mToC
  have hmBaseMapInjective : Function.Injective mBaseMap := by
    intro a b hab
    have habC : mToC a = mToC b :=
      hbaseMapInjective hab
    exact M.subtype_injective
      (L.subtype_injective
        (K.subtype_injective habC))
  have hMfixes :
      ∀ v : M,
        mBaseMap v y = y ∧ mBaseMap v z = z := by
    intro v
    have hyfix :
        fixedMap (mToK v) y = y := by
      change ((v : L) : K) • y = y
      exact MulAction.mem_stabilizer_iff.mp
        (v : L).prop
    have hzfix :
        fixedMap (mToK v) z = z := by
      change ((v : L) : K) • z = z
      exact MulAction.mem_stabilizer_iff.mp v.prop
    constructor
    · exact congrArg Subtype.val hyfix
    · exact congrArg Subtype.val hzfix
  have hsupportCardLeSeven :
      ∀ w : Equiv.Perm X,
        w.support ⊆ g.supportᶜ →
        w y = y → w z = z →
        w.support.card ≤ 7 := by
    intro w houtside hyfix hzfix
    have hyMem : y.1 ∈ g.supportᶜ := by
      rw [Finset.mem_compl]
      exact Equiv.Perm.notMem_support.mpr y.2
    have hzMem : z.1 ∈ g.supportᶜ := by
      rw [Finset.mem_compl]
      exact Equiv.Perm.notMem_support.mpr z.2
    have hyzVal : y.1 ≠ z.1 := by
      intro h
      exact hyz (Subtype.ext h)
    have hsubset :
        w.support ⊆
          (g.supportᶜ.erase y.1).erase z.1 := by
      intro x hx
      simp only [Finset.mem_erase]
      refine ⟨?_, ?_, houtside hx⟩
      · intro hxz
        apply Equiv.Perm.mem_support.mp hx
        simpa [hxz] using hzfix
      · intro hxy
        apply Equiv.Perm.mem_support.mp hx
        simpa [hxy] using hyfix
    calc
      w.support.card ≤
          ((g.supportᶜ.erase y.1).erase z.1).card :=
        Finset.card_le_card hsubset
      _ = 7 := by
        have hzErase :
            z.1 ∈ g.supportᶜ.erase y.1 :=
          Finset.mem_erase.mpr
            ⟨hyzVal.symm, hzMem⟩
        calc
          ((g.supportᶜ.erase y.1).erase z.1).card =
              (g.supportᶜ.erase y.1).card - 1 :=
            Finset.card_erase_of_mem hzErase
          _ = (g.supportᶜ.card - 1) - 1 := by
            rw [Finset.card_erase_of_mem hyMem]
          _ = 7 := by
            rw [Finset.card_compl, hcard, husupport]
  have hMdvdFull : Nat.card M ∣ 9072000 :=
    (Subgroup.card_subgroup_dvd_card M).trans
      ((Subgroup.card_subgroup_dvd_card L).trans
        hKDvdFull)
  have hprimeNotDvd :
      ∀ q : ℕ, q.Prime → (q = 2 ∨ q = 3 ∨ q = 7) →
        ¬q ∣ Nat.card M := by
    intro q hq hqCases hqdvd
    letI : Fact q.Prime := ⟨hq⟩
    obtain ⟨v, hvorder⟩ :=
      exists_prime_orderOf_dvd_card' (G := M) q hqdvd
    let vPerm : Equiv.Perm X := mBaseMap v
    have hvPermOrder : orderOf vPerm = q := by
      calc
        orderOf vPerm = orderOf v :=
          orderOf_injective mBaseMap
            hmBaseMapInjective v
        _ = q := hvorder
    have hvKer :
        mCentMap v ∈
          (Equiv.Perm.OnCycleFactors.toPermHom g).ker := by
      change
        (Equiv.Perm.OnCycleFactors.toPermHom g)
            (mCentMap v) = 1
      exact (mToK v).prop
    have hvCommutes :
        ∀ c ∈ g.cycleFactorsFinset,
          Commute vPerm c := by
      have h :=
        (Equiv.Perm.OnCycleFactors.mem_ker_toPermHom_iff
          (g := g) (mCentMap v)).mp hvKer
      intro c hc
      have hcomm := h c hc
      change Commute (mBaseMap v) c at hcomm
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
        rcases hqCases with rfl | rfl | rfl <;>
          norm_num
      have houtside :=
        PermCentralizer.support_le_compl_of_isCycle_of_commute_of_coprime_order
          hcCycle (hvCommutes c hc) hcoprime hx
      exact (Finset.mem_compl.mp houtside) hxc
    have hvSupportCard : vPerm.support.card ≤ 7 :=
      hsupportCardLeSeven vPerm hvSupport
        (hMfixes v).1 (hMfixes v).2
    have hvNe : vPerm ≠ 1 := by
      intro hv
      rw [hv, orderOf_one] at hvPermOrder
      exact hq.ne_one hvPermOrder.symm
    exact hnotAlt
      (alternatingGroup_le_of_nontrivial_support_le_seven
        X P hcard h5 (mToC v).1.prop hvNe
          hvSupportCard)
  have htwoNotDvd : ¬2 ∣ Nat.card M :=
    hprimeNotDvd 2 (by norm_num) (Or.inl rfl)
  have hthreeNotDvd : ¬3 ∣ Nat.card M :=
    hprimeNotDvd 3 (by norm_num)
      (Or.inr (Or.inl rfl))
  have hsevenNotDvd : ¬7 ∣ Nat.card M :=
    hprimeNotDvd 7 (by norm_num)
      (Or.inr (Or.inr rfl))
  have hMdvd125 : Nat.card M ∣ 125 :=
    dvd_one_twenty_five_of_dvd_double_five_kernel
      hMdvdFull htwoNotDvd hthreeNotDvd hsevenNotDvd
  have hMne125 : Nat.card M ≠ 125 := by
    intro hMcard
    let supportMap :
        M →* Equiv.Perm g.support :=
      (centralizerToSupport g).comp mCentMap
    let gSupport : Equiv.Perm g.support :=
      g.subtypePerm (fun _ => g.apply_mem_support)
    have hsupportMapMem :
        ∀ v : M, supportMap v ∈
          Subgroup.centralizer
            ({gSupport} : Set (Equiv.Perm g.support)) := by
      intro v
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Equiv.ext
      intro x
      apply Subtype.ext
      change mBaseMap v (g x.1) =
        g (mBaseMap v x.1)
      have hcomm : Commute (mBaseMap v) g := by
        exact Subgroup.mem_centralizer_singleton_iff.mp
          (mCentMap v).prop
      exact congrFun
        (congrArg DFunLike.coe hcomm.eq) x.1
    let supportCentMap :
        M →* Subgroup.centralizer
          ({gSupport} : Set (Equiv.Perm g.support)) :=
      supportMap.codRestrict
        (Subgroup.centralizer
          ({gSupport} : Set (Equiv.Perm g.support)))
        hsupportMapMem
    have hgSupportExtend :
        Equiv.Perm.ofSubtype gSupport = g := by
      exact Equiv.Perm.ofSubtype_subtypePerm
        (fun _ => g.apply_mem_support)
        (fun x hx => Equiv.Perm.mem_support.mpr hx)
    have hgSupportCycleType :
        gSupport.cycleType = g.cycleType := by
      rw [← Equiv.Perm.cycleType_ofSubtype,
        hgSupportExtend]
    have hsupportCentralizerCard :
        Nat.card
            (Subgroup.centralizer
              ({gSupport} :
                Set (Equiv.Perm g.support))) = 50 := by
      have hsupportSubtypeCard :
          Fintype.card g.support = 10 := by
        calc
          Fintype.card g.support = g.support.card :=
            Fintype.card_coe _
          _ = 10 := husupport
      rw [Equiv.Perm.nat_card_centralizer,
        hgSupportCycleType, hcycleType,
        hsupportSubtypeCard]
      norm_num
    have hrangeDvdFifty :
        Nat.card supportCentMap.range ∣ 50 := by
      rw [← hsupportCentralizerCard]
      exact Subgroup.card_subgroup_dvd_card
        supportCentMap.range
    have hsupportMul :=
      supportCentMap.ker.card_mul_index
    rw [Subgroup.index_ker] at hsupportMul
    have hrangeDvdM :
        Nat.card supportCentMap.range ∣ Nat.card M := by
      rw [← hsupportMul]
      exact dvd_mul_left _ _
    have hrangeDvdTwentyFive :
        Nat.card supportCentMap.range ∣ 25 := by
      have h :=
        Nat.dvd_gcd hrangeDvdFifty hrangeDvdM
      rw [hMcard] at h
      norm_num at h ⊢
      exact h
    have hrangeLe :
        Nat.card supportCentMap.range ≤ 25 :=
      Nat.le_of_dvd (by norm_num) hrangeDvdTwentyFive
    have hkerCard :
        1 < Nat.card supportCentMap.ker := by
      rw [hMcard] at hsupportMul
      by_contra h
      have hkerLe : Nat.card supportCentMap.ker ≤ 1 := Nat.le_of_not_gt h
      have hmulLe :
          Nat.card supportCentMap.ker * Nat.card supportCentMap.range ≤ 1 * 25 :=
        Nat.mul_le_mul hkerLe hrangeLe
      rw [hsupportMul] at hmulLe
      exact (by decide : ¬125 ≤ 1 * 25) hmulLe
    have hkerNontrivial :
        Nontrivial supportCentMap.ker :=
      Finite.one_lt_card_iff_nontrivial.mp hkerCard
    obtain ⟨v, v', hv⟩ :=
      exists_pair_ne supportCentMap.ker
    let w := v * v'⁻¹
    have hwNe : w ≠ 1 := by
      intro hw
      have := mul_inv_eq_one.mp hw
      exact hv this
    let vM : M := w
    let vPerm : Equiv.Perm X := mBaseMap vM
    have hvPermNe : vPerm ≠ 1 := by
      intro h
      apply hwNe
      exact Subtype.ext (hmBaseMapInjective h)
    have hsupportMapOne :
        supportMap vM = 1 := by
      exact congrArg Subtype.val w.prop
    have hvOutside :
        vPerm.support ⊆ g.supportᶜ := by
      intro x hx
      rw [Finset.mem_compl]
      intro hxg
      have happly :=
        congrFun (congrArg DFunLike.coe hsupportMapOne)
          (⟨x, hxg⟩ : g.support)
      have happlyVal := congrArg Subtype.val happly
      apply Equiv.Perm.mem_support.mp hx
      exact happlyVal
    have hvSupportCard : vPerm.support.card ≤ 7 :=
      hsupportCardLeSeven vPerm hvOutside
        (hMfixes vM).1 (hMfixes vM).2
    exact hnotAlt
      (alternatingGroup_le_of_nontrivial_support_le_seven
        X P hcard h5 (mToC vM).1.prop hvPermNe
          hvSupportCard)
  have hMcardLe : Nat.card M ≤ 25 :=
    le_twenty_five_of_dvd_one_twenty_five
      hMdvd125 hMne125
  have hMcardMul := M.index_mul_card
  have hLcardMul := L.index_mul_card
  have hKcardLe : Nat.card K ≤ 2025 := by
    calc
      Nat.card K = L.index * Nat.card L :=
        hLcardMul.symm
      _ = L.index * (M.index * Nat.card M) := by
        rw [hMcardMul]
      _ ≤ 9 * (9 * 25) :=
        Nat.mul_le_mul hLindexLe
          (Nat.mul_le_mul hMindexLe hMcardLe)
      _ = 2025 := by norm_num
  have hkerMul := cycleMap.ker.card_mul_index
  rw [Subgroup.index_ker] at hkerMul
  calc
    Nat.card C =
        Nat.card K * Nat.card cycleMap.range := by
      simpa only [K] using hkerMul.symm
    _ ≤ 2025 * 2 :=
      Nat.mul_le_mul hKcardLe hrangeLeTwo
    _ = 4050 := by norm_num

end FiveTransitive.Degree19

end CFSG
