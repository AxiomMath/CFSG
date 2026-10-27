module

public import CFSG.Permutation.FiveTransitive.Degree16

public section

namespace CFSG

namespace FiveTransitive.Degree16

open MulAction SubMulAction Subgroup

theorem alternatingGroup_le_of_sylow_seven_centralizer_card_eq_twenty_eight
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 16)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a → Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (S : Sylow 7 P)
    (hScard : Nat.card S = 7)
    (hCcard :
      Nat.card (Subgroup.centralizer (S : Set P)) = 28) :
    alternatingGroup X ≤ P := by
  classical
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  letI : IsCyclic S := isCyclic_of_prime_card hScard
  letI : IsMulCommutative S := IsCyclic.isMulCommutative
  obtain ⟨u, hu⟩ :=
    IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have huorder : orderOf u = 7 := hu.trans hScard
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
  have hsupportLe : g.support.card ≤ 16 := by
    calc
      g.support.card ≤ Fintype.card X :=
        Finset.card_le_univ g.support
      _ = 16 := hcard
  by_cases hsmall : g.support.card ≤ 7
  · exact alternatingGroup_le_of_prime_order_support_le_seven
      X P hcard h5 (u : P).prop (by norm_num) hgorder hsmall
  have hmTwo : m + 1 = 2 := by
    have hmLe : m + 1 ≤ 2 := by
      nlinarith
    omega
  have hcycleType : g.cycleType = {7, 7} := by
    rw [hm, hgorder, hmTwo]
    norm_num
  have hgsupport : g.support.card = 14 := by
    rw [← g.sum_cycleType, hcycleType]
    norm_num
  let C : Subgroup P :=
    Subgroup.centralizer (S : Set P)
  let baseMap : C →* Equiv.Perm X :=
    P.subtype.comp C.subtype
  have hbaseMapMem :
      ∀ q : C, baseMap q ∈
        Subgroup.centralizer ({g} : Set (Equiv.Perm X)) := by
    intro q
    change ((q.1 : P) : Equiv.Perm X) ∈
      Subgroup.centralizer ({g} : Set (Equiv.Perm X))
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val ((q.2 (u : P) u.prop).symm)
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
  have hkerMul :
      Nat.card cycleMap.ker * Nat.card cycleMap.range = 28 := by
    have h := cycleMap.ker.card_mul_index
    rw [Subgroup.index_ker] at h
    simpa only [C, hCcard] using h
  have htwoDvdKer : 2 ∣ Nat.card cycleMap.ker := by
    rcases (Nat.dvd_prime (by norm_num)).mp hrangeDvdTwo with
      hrange | hrange
    · rw [hrange, mul_one] at hkerMul
      rw [hkerMul]
      norm_num
    · rw [hrange] at hkerMul
      omega
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  obtain ⟨v, hvorder⟩ :=
    exists_prime_orderOf_dvd_card' (G := cycleMap.ker) 2 htwoDvdKer
  let vC : C := v
  let vPerm : Equiv.Perm X := baseMap vC
  have hvPermOrder : orderOf vPerm = 2 := by
    calc
      orderOf vPerm = orderOf vC :=
        orderOf_injective baseMap
          (fun _ _ h => C.subtype_injective
            (P.subtype_injective h)) vC
      _ = orderOf v := Subgroup.orderOf_coe _
      _ = 2 := hvorder
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
      norm_num
    have houtside :=
      PermCentralizer.support_le_compl_of_isCycle_of_commute_of_coprime_order
        hcCycle (hvCommutes c hc) hcoprime hx
    exact (Finset.mem_compl.mp houtside) hxc
  have hvSupportCard : vPerm.support.card ≤ 2 := by
    calc
      vPerm.support.card ≤ g.supportᶜ.card :=
        Finset.card_le_card hvSupport
      _ = 2 := by
        rw [Finset.card_compl, hcard, hgsupport]
  have hvNe : vPerm ≠ 1 := by
    intro hv
    have : orderOf vPerm = 1 :=
      orderOf_eq_one_iff.mpr hv
    omega
  exact Helpers.alternatingGroup_le_of_nontrivial_card_support_le_five
    X P h5 (by omega) (vC : P).prop hvNe (by
      change vPerm.support.card ≤ 5
      omega)

end FiveTransitive.Degree16

end CFSG
