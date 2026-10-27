module

public import CFSG.Permutation.FiveTransitive.NormalizerGoursatCycleKernel
public import CFSG.Permutation.FiveTransitive.Degree24SylowFixedAction
public import CFSG.Permutation.FiveTransitive.Degree25SmallSupport
public import CFSG.Permutation.FiveTransitive.NormalizerGoursat

public section

namespace CFSG

namespace FiveTransitive.Degree25

open MulAction SubMulAction Subgroup

private theorem order_five_mem_five_stabilizer_support_cases
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (u : fixingSubgroup P s)
    (huorder : orderOf u = 5) :
    ((((u : fixingSubgroup P s) : P) :
        Equiv.Perm X).support.card = 10) ∨
      ((((u : fixingSubgroup P s) : P) :
        Equiv.Perm X).support.card = 15) ∨
      ((((u : fixingSubgroup P s) : P) :
        Equiv.Perm X).support.card = 20) := by
  classical
  let g : Equiv.Perm X := (u : P)
  have hgorder : orderOf g = 5 := by
    calc
      orderOf g = orderOf (u : P) :=
        Subgroup.orderOf_coe _
      _ = orderOf u := Subgroup.orderOf_coe _
      _ = 5 := huorder
  have hgprime : (orderOf g).Prime := by
    rw [hgorder]
    norm_num
  obtain ⟨k, hk⟩ :=
    Equiv.Perm.cycleType_prime_order hgprime
  have hsum := g.sum_cycleType
  rw [hk, Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id, hgorder] at hsum
  have hsFixed :
      s ⊆ MulAction.fixedBy X (u : P) := by
    intro x hx
    exact
      (mem_fixingSubgroup_iff P).mp u.prop x hx
  have hfixedAtLeast :
      5 ≤ Fintype.card
        (MulAction.fixedBy X (u : P)) := by
    calc
      5 = s.ncard := hs.symm
      _ ≤ (MulAction.fixedBy X (u : P)).ncard :=
        Set.ncard_le_ncard hsFixed
      _ = Fintype.card
          (MulAction.fixedBy X (u : P)) := by
        rw [← Nat.card_coe_set_eq,
          Nat.card_eq_fintype_card]
  have hsupportLe : g.support.card ≤ 20 := by
    have huSupportLe :
        ((((u : fixingSubgroup P s) : P) :
          Equiv.Perm X).support.card ≤ 20) := by
      rw [Degree15.card_fixedBy_subgroup_perm,
        hcard] at hfixedAtLeast
      omega
    exact huSupportLe
  have hkCases :
      k + 1 = 1 ∨ k + 1 = 2 ∨
        k + 1 = 3 ∨ k + 1 = 4 := by
    have hkLe : k + 1 ≤ 4 := by
      by_contra hle
      have hfive : 5 ≤ k + 1 := by omega
      have htwentyFive :
          25 ≤ g.support.card := by
        calc
          25 = 5 * 5 := by norm_num
          _ ≤ (k + 1) * 5 :=
            Nat.mul_le_mul_right 5 hfive
          _ = g.support.card := hsum
      omega
    omega
  rcases hkCases with hkOne | hkTwo | hkThree | hkFour
  · have hsupport : g.support.card = 5 := by
      omega
    exact False.elim
      (hnotAlt
        (alternatingGroup_le_of_nontrivial_support_le_seven
          X P hcard h5 ((u : P).prop)
          (by
            intro hu
            have huP : (u : P) = 1 :=
              Subtype.ext hu
            have hgOne : g = 1 := by
              change ((u : P) : Equiv.Perm X) = 1
              exact congrArg Subtype.val huP
            rw [hgOne, orderOf_one] at hgorder
            norm_num at hgorder)
          (by
            change g.support.card ≤ 7
            omega)))
  · left
    simpa only [g] using
      (show g.support.card = 10 by omega)
  · right
    left
    simpa only [g] using
      (show g.support.card = 15 by omega)
  · right
    right
    simpa only [g] using
      (show g.support.card = 20 by omega)

theorem alternatingGroup_le_of_sylow_five_card_five
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 25)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 5 (fixingSubgroup P s))
    (hScard : Nat.card S = 5) :
    alternatingGroup X ≤ P := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let H : Subgroup P := fixingSubgroup P s
  let R : Subgroup P :=
    Degree24.sylowImage X P s S
  let N : Subgroup P :=
    Subgroup.normalizer (R : Set P)
  let SN : Subgroup N :=
    R.subgroupOf N
  let F := MulAction.fixedPoints SN X
  let ρ : N →* Equiv.Perm F :=
    MulAction.toPermHom N F
  letI : IsCyclic S :=
    isCyclic_of_prime_card hScard
  obtain ⟨u, huRaw⟩ :=
    IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have huOrder : orderOf u = 5 :=
    huRaw.trans hScard
  have huNe : u ≠ 1 := by
    intro huOne
    rw [huOne, orderOf_one] at huOrder
    omega
  let r : R :=
    ⟨((u : H) : P),
      Subgroup.mem_map_of_mem H.subtype u.prop⟩
  let g : Equiv.Perm X := ((u : H) : P)
  have hgOrder : orderOf g = 5 := by
    change
      orderOf ((((u : H) : P) : Equiv.Perm X)) = 5
    calc
      orderOf ((((u : H) : P) : Equiv.Perm X)) =
          orderOf ((u : H) : P) :=
        Subgroup.orderOf_coe _
      _ = orderOf (u : H) :=
        Subgroup.orderOf_coe _
      _ = orderOf u :=
        Subgroup.orderOf_coe _
      _ = 5 := huOrder
  have hfixed :
      F = Function.fixedPoints g := by
    simpa only [H, R, N, SN, F, r, g] using
      Degree24.sylowFixedPoints_eq_fixedPoints_generator
        X P s S hScard u huNe
  have hsupportCases :
      g.support.card = 10 ∨
        g.support.card = 15 ∨
        g.support.card = 20 := by
    simpa only [H, g] using
      order_five_mem_five_stabilizer_support_cases
        X P hcard h5 hnotAlt s hs (u : H) (by
          calc
            orderOf (u : H) = orderOf u :=
              Subgroup.orderOf_coe _
            _ = 5 := huOrder)
  have hFcases :
      Nat.card F = 15 ∨ Nat.card F = 10 ∨
        Nat.card F = 5 := by
    rcases hsupportCases with hten | hfifteen | htwenty
    · left
      rw [hfixed, Nat.card_eq_fintype_card,
        Equiv.Perm.card_fixedPoints,
        Equiv.Perm.sum_cycleType, hcard, hten]
    · right
      left
      rw [hfixed, Nat.card_eq_fintype_card,
        Equiv.Perm.card_fixedPoints,
        Equiv.Perm.sum_cycleType, hcard, hfifteen]
    · right
      right
      rw [hfixed, Nat.card_eq_fintype_card,
        Equiv.Perm.card_fixedPoints,
        Equiv.Perm.sum_cycleType, hcard, htwenty]
  let J : Subgroup (Equiv.Perm F) :=
    ρ.range
  have hJ5 :
      ∀ a b : Fin 5 → F, Function.Injective a →
        Function.Injective b →
        ∃ q : J, ∀ i, q • a i = b i := by
    intro a b ha hb
    obtain ⟨q, hq⟩ :=
      Degree24.sylowNormalizer_five_transitive_on_fixedPoints
        X P h5 s hs S a b ha hb
    exact ⟨⟨ρ q, ⟨q, rfl⟩⟩, hq⟩
  have hNestedLe :
      (MulAction.toPermHom J F).range ≤ J := by
    intro q hq
    obtain ⟨j, hj⟩ := hq
    rw [← hj]
    exact j.prop
  let eSR : S ≃* R :=
    (S : Subgroup H).equivMapOfInjective
      H.subtype H.subtype_injective
  have hAutS :
      Nat.card (MulAut S) = 4 := by
    rw [IsCyclic.card_mulAut S, hScard,
      Nat.totient_prime (by norm_num)]
  have hAutR :
      Nat.card (MulAut R) = 4 := by
    calc
      Nat.card (MulAut R) =
          Nat.card (MulAut S) :=
        Nat.card_congr
          (MulAut.congr eSR.symm).toEquiv
      _ = 4 := hAutS
  let gSupport : Equiv.Perm g.support :=
    g.subtypePerm (fun _ => g.apply_mem_support)
  have hgSupportExtend :
      Equiv.Perm.ofSubtype gSupport = g :=
    Equiv.Perm.ofSubtype_subtypePerm
      (fun _ => g.apply_mem_support)
      (fun x hx => Equiv.Perm.mem_support.mpr hx)
  have hgSupportCycleType :
      gSupport.cycleType = g.cycleType := by
    rw [← Equiv.Perm.cycleType_ofSubtype,
      hgSupportExtend]
  have hgPrime : (orderOf g).Prime := by
    rw [hgOrder]
    norm_num
  obtain ⟨k, hk⟩ :=
    Equiv.Perm.cycleType_prime_order hgPrime
  have hcore
      (hAlt : alternatingGroup F ≤ ρ.range)
      (hAutSmall :
        Nat.card (MulAut R) <
          Nat.card (alternatingGroup F))
      (hSupportSmall :
        Nat.card
            (Subgroup.centralizer
              ({gSupport} :
                Set (Equiv.Perm g.support))) <
          Nat.card (alternatingGroup F)) :
      alternatingGroup X ≤ P := by
    apply
      FiveTransitive.NormalizerGoursat.alternatingGroup_le_of_fixed_action
        X P (by omega) h5 R r
    · simpa only [N, SN, F, g, r] using hfixed
    · have hfiveF : 5 ≤ Fintype.card F := by
        rcases hFcases with hF | hF | hF
        all_goals rw [Nat.card_eq_fintype_card] at hF
        all_goals omega
      simpa only [N, SN, F] using hfiveF
    · simpa only [N, SN, F, ρ] using hAlt
    · simpa only [N, SN, F, hAutR] using hAutSmall
    · simpa only [N, SN, F, g, gSupport] using
        hSupportSmall
  rcases hFcases with hFfifteen | hFten | hFfive
  · have hFtype : Fintype.card F = 15 := by
      rw [← Nat.card_eq_fintype_card]
      exact hFfifteen
    have hAlt :
        alternatingGroup F ≤ ρ.range := by
      change alternatingGroup F ≤ J
      exact
        Degree15.alternatingGroup_le_of_five_transitive_of_card_eq_fifteen
          F J hFtype hJ5
    have hAltCard :
        Nat.card (alternatingGroup F) =
          653837184000 := by
      letI : Nontrivial F :=
        Fintype.one_lt_card_iff_nontrivial.mp (by
          rw [hFtype]
          norm_num)
      rw [Nat.card_eq_fintype_card,
        card_alternatingGroup, hFtype]
      norm_num
    have hgSupport : g.support.card = 10 := by
      have hfixedFormula :=
        Equiv.Perm.card_fixedPoints g
      rw [hcard, Equiv.Perm.sum_cycleType] at hfixedFormula
      have hfixedCard :
          Fintype.card (Function.fixedPoints g) = 15 := by
        rw [← Nat.card_eq_fintype_card,
          Nat.card_coe_set_eq]
        have hfixedNcard :=
          congrArg Set.ncard hfixed
        have hFncard : F.ncard = 15 := by
          rw [← Nat.card_coe_set_eq]
          exact hFfifteen
        omega
      rw [hfixedCard] at hfixedFormula
      omega
    have hsum := g.sum_cycleType
    rw [hk, Multiset.sum_replicate,
      nsmul_eq_mul, Nat.cast_id,
      hgOrder, hgSupport] at hsum
    have hkTwo : k + 1 = 2 := by omega
    have hgCycleType :
        g.cycleType = {5, 5} := by
      rw [hk, hgOrder, hkTwo]
      norm_num
    have hsupportTypeCard :
        Fintype.card g.support = 10 := by
      rw [Fintype.card_coe, hgSupport]
    have hSupportCentralizer :
        Nat.card
            (Subgroup.centralizer
              ({gSupport} :
                Set (Equiv.Perm g.support))) = 50 := by
      rw [Equiv.Perm.nat_card_centralizer,
        hgSupportCycleType, hgCycleType,
        hsupportTypeCard]
      norm_num
    apply hcore hAlt
    · rw [hAutR, hAltCard]
      norm_num
    · rw [hSupportCentralizer, hAltCard]
      norm_num
  · have hFtype : Fintype.card F = 10 := by
      rw [← Nat.card_eq_fintype_card]
      exact hFten
    have hAltNested :
        alternatingGroup F ≤
          (MulAction.toPermHom J F).range :=
      Helpers.alternatingGroup_le_of_five_transitive_of_card_eq_ten
        J F hFtype hJ5
    have hAlt :
        alternatingGroup F ≤ ρ.range :=
      hAltNested.trans hNestedLe
    have hAltCard :
        Nat.card (alternatingGroup F) = 1814400 := by
      letI : Nontrivial F :=
        Fintype.one_lt_card_iff_nontrivial.mp (by
          rw [hFtype]
          norm_num)
      rw [Nat.card_eq_fintype_card,
        card_alternatingGroup, hFtype]
      norm_num
    have hgSupport : g.support.card = 15 := by
      have hfixedFormula :=
        Equiv.Perm.card_fixedPoints g
      rw [hcard, Equiv.Perm.sum_cycleType] at hfixedFormula
      have hfixedCard :
          Fintype.card (Function.fixedPoints g) = 10 := by
        rw [← Nat.card_eq_fintype_card,
          Nat.card_coe_set_eq]
        have hfixedNcard :=
          congrArg Set.ncard hfixed
        have hFncard : F.ncard = 10 := by
          rw [← Nat.card_coe_set_eq]
          exact hFten
        omega
      rw [hfixedCard] at hfixedFormula
      omega
    have hsum := g.sum_cycleType
    rw [hk, Multiset.sum_replicate,
      nsmul_eq_mul, Nat.cast_id,
      hgOrder, hgSupport] at hsum
    have hkThree : k + 1 = 3 := by omega
    have hgCycleType :
        g.cycleType = {5, 5, 5} := by
      rw [hk, hgOrder, hkThree]
      norm_num
    have hsupportTypeCard :
        Fintype.card g.support = 15 := by
      rw [Fintype.card_coe, hgSupport]
    have hSupportCentralizer :
        Nat.card
            (Subgroup.centralizer
              ({gSupport} :
                Set (Equiv.Perm g.support))) = 750 := by
      rw [Equiv.Perm.nat_card_centralizer,
        hgSupportCycleType, hgCycleType,
        hsupportTypeCard]
      norm_num
    apply hcore hAlt
    · rw [hAutR, hAltCard]
      norm_num
    · rw [hSupportCentralizer, hAltCard]
      norm_num
  · have hFtype : Fintype.card F = 5 := by
      rw [← Nat.card_eq_fintype_card]
      exact hFfive
    have hJmt :
        MulAction.IsMultiplyPretransitive J F 5 := by
      rw [MulAction.isMultiplyPretransitive_iff]
      intro a b
      obtain ⟨q, hq⟩ :=
        hJ5 a b a.injective b.injective
      refine ⟨q, ?_⟩
      ext i
      exact congrArg Subtype.val (hq i)
    have hJfour :
        MulAction.IsMultiplyPretransitive J F 4 := by
      letI : MulAction.IsMultiplyPretransitive J F 5 := hJmt
      apply MulAction.isMultiplyPretransitive_of_le
        (G := J) (α := F) (m := 4) (n := 5)
      · norm_num
      · simp [Nat.card_eq_fintype_card, hFtype]
    have hJtop : J = ⊤ := by
      apply Equiv.Perm.eq_top_of_isMultiplyPretransitive
      simp only [Nat.card_eq_fintype_card, hFtype]
      exact hJfour
    have hAlt :
        alternatingGroup F ≤ ρ.range := by
      change alternatingGroup F ≤ J
      rw [hJtop]
      exact le_top
    have hAltCard :
        Nat.card (alternatingGroup F) = 60 := by
      letI : Nontrivial F :=
        Fintype.one_lt_card_iff_nontrivial.mp (by
          rw [hFtype]
          norm_num)
      rw [Nat.card_eq_fintype_card,
        card_alternatingGroup, hFtype]
      norm_num
    have hgSupport : g.support.card = 20 := by
      have hfixedFormula :=
        Equiv.Perm.card_fixedPoints g
      rw [hcard, Equiv.Perm.sum_cycleType] at hfixedFormula
      have hfixedCard :
          Fintype.card (Function.fixedPoints g) = 5 := by
        rw [← Nat.card_eq_fintype_card,
          Nat.card_coe_set_eq]
        have hfixedNcard :=
          congrArg Set.ncard hfixed
        have hFncard : F.ncard = 5 := by
          rw [← Nat.card_coe_set_eq]
          exact hFfive
        omega
      rw [hfixedCard] at hfixedFormula
      omega
    have hsum := g.sum_cycleType
    rw [hk, Multiset.sum_replicate,
      nsmul_eq_mul, Nat.cast_id,
      hgOrder, hgSupport] at hsum
    have hkFour : k + 1 = 4 := by omega
    have hgCycleType :
        g.cycleType = {5, 5, 5, 5} := by
      rw [hk, hgOrder, hkFour]
      norm_num
    have hsupportTypeCard :
        Fintype.card g.support = 20 := by
      rw [Fintype.card_coe, hgSupport]
    have hcycleFactorsCard :
        Fintype.card gSupport.cycleFactorsFinset = 4 := by
      rw [Fintype.card_coe]
      have hcardCycles :=
        congrArg Multiset.card hgSupportCycleType
      rw [Equiv.Perm.cycleType,
        Multiset.card_map, hgCycleType] at hcardCycles
      norm_num at hcardCycles ⊢
      exact hcardCycles
    have hCyclePermCard :
        Nat.card
            (Equiv.Perm gSupport.cycleFactorsFinset) = 24 := by
      rw [Nat.card_perm, Nat.card_eq_fintype_card,
        hcycleFactorsCard]
      norm_num
    have hKernelCard :
        Nat.card
            (Equiv.Perm.OnCycleFactors.toPermHom
              gSupport).ker = 625 := by
      have hRangeCard :
          Fintype.card
              (Equiv.Perm.OnCycleFactors.kerParam
                gSupport).range = 625 := by
        rw [
        Equiv.Perm.OnCycleFactors.kerParam_range_card,
        hsupportTypeCard, hgSupportCycleType,
        hgCycleType]
        norm_num
      have hRangeEq :
          Fintype.card
              (Equiv.Perm.OnCycleFactors.kerParam
                gSupport).range =
            Nat.card
              (Equiv.Perm.OnCycleFactors.toPermHom
                gSupport).ker := by
        rw [← Nat.card_eq_fintype_card,
          Equiv.Perm.OnCycleFactors.kerParam_range_eq,
          Subgroup.card_subtype]
      omega
    apply
      FiveTransitive.NormalizerGoursat.alternatingGroup_le_of_fixed_action_cycle_kernel
        X P (by omega) h5 R r
    · simpa only [N, SN, F, g, r] using hfixed
    · change 5 ≤ Fintype.card F
      rw [hFtype]
    · simpa only [N, SN, F, ρ] using hAlt
    · change
        Nat.card (MulAut R) <
          Nat.card (alternatingGroup F)
      rw [hAutR, hAltCard]
      norm_num
    · change
        Nat.card
            (FiveTransitive.NormalizerGoursat.centralizerCycleMap
              X P R r).range <
          Nat.card (alternatingGroup F)
      calc
        Nat.card
              (FiveTransitive.NormalizerGoursat.centralizerCycleMap
                X P R r).range ≤
            Nat.card
              (Equiv.Perm gSupport.cycleFactorsFinset) :=
          Nat.le_of_dvd Nat.card_pos
            (Subgroup.card_subgroup_dvd_card _)
        _ = 24 := hCyclePermCard
        _ < Nat.card (alternatingGroup F) := by
          rw [hAltCard]
          norm_num
    · change
        ¬Nat.card (alternatingGroup F) ∣
          Nat.card
            (Equiv.Perm.OnCycleFactors.toPermHom
              gSupport).ker
      rw [hKernelCard, hAltCard]
      norm_num

end FiveTransitive.Degree25

end CFSG
