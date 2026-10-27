module

public import CFSG.Permutation.FiveTransitive.Degree24PrimeSupportIncidence
public import CFSG.Permutation.FiveTransitive.NormalizerGoursat
public import CFSG.Permutation.FiveTransitive.Degree24FiveFixedAction

public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

private theorem alternatingGroup_le_of_sylow_five_card_five
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
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
    (S : Subgroup H).map H.subtype
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
      sylowFixedPoints_eq_fixedPoints_generator
        X P s S hScard u huNe
  have hFcases :
      Nat.card F = 9 ∨ Nat.card F = 14 := by
    simpa only [H, R, N, SN, F] using
      sylow_five_fixedPoints_card_eq_nine_or_fourteen
        X P hcard h5 hnotAlt s hs S hScard
  let J : Subgroup (Equiv.Perm F) :=
    ρ.range
  have hJ5 :
      ∀ a b : Fin 5 → F, Function.Injective a →
        Function.Injective b →
        ∃ q : J, ∀ i, q • a i = b i := by
    intro a b ha hb
    obtain ⟨q, hq⟩ :=
      sylowNormalizer_five_transitive_on_fixedPoints
        X P h5 s hs S a b ha hb
    let qJ : J := ⟨ρ q, ⟨q, rfl⟩⟩
    refine ⟨qJ, ?_⟩
    intro i
    exact hq i
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
      Equiv.Perm.ofSubtype gSupport = g := by
    exact Equiv.Perm.ofSubtype_subtypePerm
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
      (hFcard : Nat.card F = 9 ∨ Nat.card F = 14)
      (hAlt : alternatingGroup F ≤ ρ.range)
      (hAutSmall :
        4 < Nat.card (alternatingGroup F))
      (hSupportSmall :
        Nat.card
            (Subgroup.centralizer
              ({gSupport} :
                Set (Equiv.Perm g.support))) <
          Nat.card (alternatingGroup F)) :
      alternatingGroup X ≤ P := by
    have hFcard' :
        Fintype.card F = 9 ∨
          Fintype.card F = 14 := by
      rcases hFcard with hFcard | hFcard
      · left
        rw [← Nat.card_eq_fintype_card]
        exact hFcard
      · right
        rw [← Nat.card_eq_fintype_card]
        exact hFcard
    have hFiveF : 5 ≤ Fintype.card F := by
      omega
    apply
      FiveTransitive.NormalizerGoursat.alternatingGroup_le_of_fixed_action
        X P (by omega) h5 R r
    · simpa only [N, SN, F, g, r] using hfixed
    · simpa only [N, SN, F] using hFiveF
    · simpa only [N, SN, F, ρ] using hAlt
    · dsimp only
      change
        Nat.card (MulAut R) <
          Nat.card (alternatingGroup F)
      rw [hAutR]
      exact hAutSmall
    · dsimp only
      change
        Nat.card
            (Subgroup.centralizer
              ({gSupport} :
                Set (Equiv.Perm g.support))) <
          Nat.card (alternatingGroup F)
      exact hSupportSmall
  rcases hFcases with hFnine | hFfourteen
  · have hFtype : Fintype.card F = 9 := by
      rw [← Nat.card_eq_fintype_card]
      exact hFnine
    have hAltNested :
        alternatingGroup F ≤
          (MulAction.toPermHom J F).range :=
      Helpers.alternatingGroup_le_of_five_transitive_of_card_eq_nine
        J F hFtype hJ5
    have hAlt :
        alternatingGroup F ≤ ρ.range :=
      hAltNested.trans hNestedLe
    have hAltCard :
        Nat.card (alternatingGroup F) = 181440 := by
      letI : Nontrivial F :=
        Fintype.one_lt_card_iff_nontrivial.mp (by
          rw [hFtype]
          norm_num)
      rw [Nat.card_eq_fintype_card,
        card_alternatingGroup, hFtype]
      norm_num
    have hfixedG :
        Fintype.card
          (Function.fixedPoints g) = 9 := by
      rw [← Nat.card_eq_fintype_card,
        Nat.card_coe_set_eq]
      have hfixedNcard :=
        congrArg Set.ncard hfixed
      have hFncard : F.ncard = 9 := by
        rw [← Nat.card_coe_set_eq]
        exact hFnine
      omega
    have hgSupport : g.support.card = 15 := by
      have hfixedFormula :=
        Equiv.Perm.card_fixedPoints g
      rw [hcard, Equiv.Perm.sum_cycleType] at hfixedFormula
      omega
    have hsum := g.sum_cycleType
    rw [hk, Multiset.sum_replicate,
      nsmul_eq_mul, Nat.cast_id,
      hgOrder, hgSupport] at hsum
    have hkThree : k + 1 = 3 := by
      omega
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
    apply hcore
    · exact Or.inl hFnine
    · exact hAlt
    · rw [hAltCard]
      norm_num
    · rw [hSupportCentralizer, hAltCard]
      norm_num
  · have hFtype : Fintype.card F = 14 := by
      rw [← Nat.card_eq_fintype_card]
      exact hFfourteen
    have hAlt :
        alternatingGroup F ≤ ρ.range := by
      change alternatingGroup F ≤ J
      exact
        Degree14.alternatingGroup_le_of_five_transitive_of_card_eq_fourteen
          F J hFtype hJ5
    have hAltCard :
        Nat.card (alternatingGroup F) =
          43589145600 := by
      letI : Nontrivial F :=
        Fintype.one_lt_card_iff_nontrivial.mp (by
          rw [hFtype]
          norm_num)
      rw [Nat.card_eq_fintype_card,
        card_alternatingGroup, hFtype]
      norm_num
    have hfixedG :
        Fintype.card
          (Function.fixedPoints g) = 14 := by
      rw [← Nat.card_eq_fintype_card,
        Nat.card_coe_set_eq]
      have hfixedNcard :=
        congrArg Set.ncard hfixed
      have hFncard : F.ncard = 14 := by
        rw [← Nat.card_coe_set_eq]
        exact hFfourteen
      omega
    have hgSupport : g.support.card = 10 := by
      have hfixedFormula :=
        Equiv.Perm.card_fixedPoints g
      rw [hcard, Equiv.Perm.sum_cycleType] at hfixedFormula
      omega
    have hsum := g.sum_cycleType
    rw [hk, Multiset.sum_replicate,
      nsmul_eq_mul, Nat.cast_id,
      hgOrder, hgSupport] at hsum
    have hkTwo : k + 1 = 2 := by
      omega
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
    apply hcore
    · exact Or.inr hFfourteen
    · exact hAlt
    · rw [hAltCard]
      norm_num
    · rw [hSupportCentralizer, hAltCard]
      norm_num

theorem five_point_stabilizer_card_ne_remaining_five_cases
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 24)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (hHcard :
      Nat.card (fixingSubgroup P s) = 360 ∨
      Nat.card (fixingSubgroup P s) = 1280 ∨
      Nat.card (fixingSubgroup P s) = 30720) :
    False := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let H : Subgroup P := fixingSubgroup P s
  let S : Sylow 5 H := Sylow.nonempty.some
  have hScard : Nat.card S = 5 := by
    rcases hHcard with h360 | h1280 | h30720
    · exact
        sylow_card_eq_prime_of_card_eq_prime_mul
          H 5 72 (by norm_num) (by norm_num)
            (by simpa only [H] using h360) S
    · exact
        sylow_card_eq_prime_of_card_eq_prime_mul
          H 5 256 (by norm_num) (by norm_num)
            (by simpa only [H] using h1280) S
    · exact
        sylow_card_eq_prime_of_card_eq_prime_mul
          H 5 6144 (by norm_num) (by norm_num)
            (by simpa only [H] using h30720) S
  exact
    hnotAlt
      (alternatingGroup_le_of_sylow_five_card_five
        X P hcard h5 hnotAlt s hs S hScard)

end FiveTransitive.Degree24

end CFSG
