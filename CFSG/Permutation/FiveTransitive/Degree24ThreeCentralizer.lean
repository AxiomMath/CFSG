module

public import CFSG.Permutation.FiveTransitive.Degree24StabilizerFixedPoints

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

private theorem order_five_support_eq_twenty_of_stabilizer_card_not_dvd_five
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (s : Set X) (hs : s.ncard = 5)
    (hnotFive :
      ¬5 ∣ Nat.card (fixingSubgroup P s))
    (u : P) (huorder : orderOf u = 5) :
    (u : Equiv.Perm X).support.card = 20 := by
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
  have hsupportLe : g.support.card ≤ 24 := by
    calc
      g.support.card ≤ Fintype.card X :=
        Finset.card_le_univ g.support
      _ = 24 := hcard
  have hnotSupportLe : ¬g.support.card ≤ 15 := by
    intro hsupport
    have hfixedCard :
        5 ≤ Fintype.card (Function.fixedPoints g) := by
      rw [Equiv.Perm.card_fixedPoints,
        Equiv.Perm.sum_cycleType, hcard]
      omega
    let e : Fin 5 ↪ Function.fixedPoints g :=
      Classical.choice
        (Function.Embedding.nonempty_of_card_le
          hfixedCard)
    let eX : Fin 5 ↪ X :=
      e.trans (Function.Embedding.subtype _)
    let t : Set X := Set.range eX
    have ht : t.ncard = 5 := by
      rw [Set.ncard_range_of_injective eX.injective,
        Nat.card_eq_fintype_card, Fintype.card_fin]
    let uT : fixingSubgroup P t :=
      ⟨u, by
        rw [mem_fixingSubgroup_iff]
        rintro _ ⟨i, rfl⟩
        exact (e i).2⟩
    have huTorder : orderOf uT = 5 := by
      calc
        orderOf uT = orderOf (uT : P) :=
          (Subgroup.orderOf_coe _).symm
        _ = orderOf u := rfl
        _ = 5 := huorder
    have hfiveT :
        5 ∣ Nat.card (fixingSubgroup P t) := by
      rw [← huTorder, Nat.card_eq_fintype_card]
      exact orderOf_dvd_card
    have hequal :
        Nat.card (fixingSubgroup P s) =
          Nat.card (fixingSubgroup P t) :=
      five_point_stabilizers_have_equal_card
        X P h5 s t hs ht
    apply hnotFive
    rw [hequal]
    exact hfiveT
  have hsupportEq :
      (k + 1) * 5 = g.support.card :=
    hsum
  have hkFour : k + 1 = 4 := by
    omega
  rw [← hsupportEq, hkFour]

theorem five_not_dvd_centralizer_of_subgroup_card_nine
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (hnotFive :
      ¬5 ∣ Nat.card (fixingSubgroup P s))
    (S : Subgroup P) (hScard : Nat.card S = 9) :
    ¬5 ∣ Nat.card
      (Subgroup.centralizer (S : Set P)) := by
  classical
  intro hfive
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let C : Subgroup P :=
    Subgroup.centralizer (S : Set P)
  obtain ⟨u, huorder⟩ :=
    exists_prime_orderOf_dvd_card' (G := C) 5 hfive
  let uP : P := u
  let g : Equiv.Perm X := uP
  have huPorder : orderOf uP = 5 := by
    calc
      orderOf uP = orderOf u := Subgroup.orderOf_coe _
      _ = 5 := huorder
  have hgsupport : g.support.card = 20 := by
    simpa only [g, uP] using
      order_five_support_eq_twenty_of_stabilizer_card_not_dvd_five
        X P hcard h5 s hs hnotFive uP huPorder
  have hgorder : orderOf g = 5 := by
    calc
      orderOf g = orderOf uP := Subgroup.orderOf_coe _
      _ = 5 := huPorder
  have hgprime : (orderOf g).Prime := by
    rw [hgorder]
    norm_num
  obtain ⟨k, hk⟩ :=
    Equiv.Perm.cycleType_prime_order hgprime
  have hsum := g.sum_cycleType
  rw [hk, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, hgorder, hgsupport] at hsum
  have hkFour : k + 1 = 4 := by omega
  have hcycleType :
      g.cycleType = {5, 5, 5, 5} := by
    rw [hk, hgorder, hkFour]
    norm_num
  let baseMap : S →* Equiv.Perm X :=
    P.subtype.comp S.subtype
  have hbaseMapInjective :
      Function.Injective baseMap := by
    intro a b hab
    exact S.subtype_injective
      (P.subtype_injective hab)
  have hbaseMapMem :
      ∀ z : S, baseMap z ∈
        Subgroup.centralizer
          ({g} : Set (Equiv.Perm X)) := by
    intro z
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcommP :
        (z : P) * uP = uP * (z : P) :=
      (Subgroup.mem_centralizer_iff.mp u.prop)
        z z.prop
    exact congrArg Subtype.val hcommP
  let centMap :
      S →* Subgroup.centralizer
        ({g} : Set (Equiv.Perm X)) :=
    baseMap.codRestrict
      (Subgroup.centralizer
        ({g} : Set (Equiv.Perm X)))
      hbaseMapMem
  have hcentMapInjective :
      Function.Injective centMap := by
    intro a b hab
    have hab' := congrArg Subtype.val hab
    exact hbaseMapInjective hab'
  let cycleMap :
      S →* Equiv.Perm g.cycleFactorsFinset :=
    (Equiv.Perm.OnCycleFactors.toPermHom g).comp
      centMap
  have hcycleFactorCard :
      Fintype.card g.cycleFactorsFinset = 4 := by
    have h :=
      congrArg Multiset.card
        (Equiv.Perm.cycleType_def g)
    rw [hcycleType] at h
    simpa using h.symm
  have hcyclePermCard :
      Nat.card
          (Equiv.Perm g.cycleFactorsFinset) = 24 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card,
      hcycleFactorCard]
    norm_num
  have hcycleMapNotInjective :
      ¬Function.Injective cycleMap := by
    intro hinjective
    have hdvd :=
      Subgroup.card_dvd_of_injective
        cycleMap hinjective
    rw [hScard, hcyclePermCard] at hdvd
    norm_num at hdvd
  let K : Subgroup S := cycleMap.ker
  have hKne : K ≠ ⊥ := by
    intro hK
    exact hcycleMapNotInjective
      ((MonoidHom.ker_eq_bot_iff cycleMap).mp hK)
  have hKnontrivial : Nontrivial K :=
    K.nontrivial_iff_ne_bot.mpr hKne
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hSisP : IsPGroup 3 S := by
    apply IsPGroup.of_card (n := 2)
    rw [hScard]
    norm_num
  have hKisP : IsPGroup 3 K :=
    hSisP.to_subgroup K
  have hKcardGt : 1 < Nat.card K :=
    Finite.one_lt_card_iff_nontrivial.mpr
      hKnontrivial
  have hthreeDvdK : 3 ∣ Nat.card K :=
    hKisP.card_eq_or_dvd.resolve_left
      (ne_of_gt hKcardGt)
  obtain ⟨v, hvorder⟩ :=
    exists_prime_orderOf_dvd_card'
      (G := K) 3 hthreeDvdK
  let vS : S := v
  let vPerm : Equiv.Perm X := baseMap vS
  have hvPermOrder : orderOf vPerm = 3 := by
    calc
      orderOf vPerm = orderOf vS :=
        orderOf_injective baseMap
          hbaseMapInjective vS
      _ = orderOf v := Subgroup.orderOf_coe _
      _ = 3 := hvorder
  have hvKer :
      centMap vS ∈
        (Equiv.Perm.OnCycleFactors.toPermHom g).ker := by
    change
      (Equiv.Perm.OnCycleFactors.toPermHom g)
          (centMap vS) = 1
    exact v.prop
  have hvCommutes :
      ∀ c ∈ g.cycleFactorsFinset,
        Commute vPerm c := by
    have hcommutes :=
      (Equiv.Perm.OnCycleFactors.mem_ker_toPermHom_iff
        (g := g) (centMap vS)).mp hvKer
    intro c hc
    have hcomm := hcommutes c hc
    change Commute (baseMap vS) c at hcomm
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
            ({5, 5, 5, 5} : Multiset ℕ) :=
        Multiset.mem_of_le hcTypeLe (by simp)
      simpa using hmem
    have hcOrder : orderOf c = 5 := by
      rw [hcCycle.orderOf, hcSupport]
    have hcoprime :
        Nat.Coprime (orderOf vPerm) (orderOf c) := by
      rw [hvPermOrder, hcOrder]
      norm_num
    have houtside :=
      PermCentralizer.support_le_compl_of_isCycle_of_commute_of_coprime_order
        hcCycle (hvCommutes c hc) hcoprime hx
    exact (Finset.mem_compl.mp houtside) hxc
  have hvSupportCard : vPerm.support.card ≤ 4 := by
    calc
      vPerm.support.card ≤ g.supportᶜ.card :=
        Finset.card_le_card hvSupport
      _ = 4 := by
        rw [Finset.card_compl, hcard, hgsupport]
  have hvNe : vPerm ≠ 1 := by
    intro hv
    rw [hv, orderOf_one] at hvPermOrder
    norm_num at hvPermOrder
  exact hnotAlt
    (alternatingGroup_le_of_nontrivial_support_le_seven
      X P hcard h5 vS.1.prop hvNe (by
        change vPerm.support.card ≤ 7
        omega))

end FiveTransitive.Degree24

end CFSG
