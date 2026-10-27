module

public import CFSG.Permutation.FiveTransitive.Degree28BlockEscape
public import CFSG.Permutation.FiveTransitive.SmallDegreeFixedAction

public section

namespace CFSG

namespace FiveTransitive.Degree28WitnessClosure

open Subgroup MulAction

private theorem alternatingGroup_le_cyclic_fixed_range
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hdegree : 5 ≤ Fintype.card X)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b → ∃ q : P, ∀ i, q • a i = b i)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 3 (fixingSubgroup P s))
    (r : P)
    [Fintype
      (FiveTransitive.PrimeCyclicFixedAction.cyclicFixedPoints X P r)]
    (hRSP :
      FiveTransitive.PrimeCyclicFixedAction.cyclicSubgroup P r =
        FiveTransitive.Degree24.sylowImage X P s S)
    (hfixedFive :
      5 ≤ Fintype.card
        (FiveTransitive.PrimeCyclicFixedAction.cyclicFixedPoints X P r))
    (hfixedUpper :
      Fintype.card
          (FiveTransitive.PrimeCyclicFixedAction.cyclicFixedPoints X P r) ≤ 27)
    (hfixedNotTwelve :
      Fintype.card
          (FiveTransitive.PrimeCyclicFixedAction.cyclicFixedPoints X P r) ≠ 12)
    (hfixedNotTwentyFour :
      Fintype.card
          (FiveTransitive.PrimeCyclicFixedAction.cyclicFixedPoints X P r) ≠ 24) :
    alternatingGroup
        (FiveTransitive.PrimeCyclicFixedAction.cyclicFixedPoints X P r) ≤
      (MulAction.toPermHom
        (FiveTransitive.PrimeCyclicFixedAction.cyclicNormalizer P r)
        (FiveTransitive.PrimeCyclicFixedAction.cyclicFixedPoints X P r)).range := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let R : Subgroup P :=
    FiveTransitive.PrimeCyclicFixedAction.cyclicSubgroup P r
  let N : Subgroup P :=
    FiveTransitive.PrimeCyclicFixedAction.cyclicNormalizer P r
  let F := FiveTransitive.PrimeCyclicFixedAction.cyclicFixedPoints X P r
  let J : Subgroup (Equiv.Perm F) :=
    (MulAction.toPermHom N F).range
  have hNfive :
      ∀ a b : Fin 5 → F, Function.Injective a →
        Function.Injective b → ∃ q : N, ∀ i, q • a i = b i := by
    let SP : Subgroup P :=
      FiveTransitive.Degree24.sylowImage X P s S
    have htransport
        (R' : Subgroup P) (hR' : R' = SP) :
        ∀ a b : Fin 5 →
            MulAction.fixedPoints
              (R'.subgroupOf
                (Subgroup.normalizer (R' : Set P))) X,
          Function.Injective a → Function.Injective b →
          ∃ q : Subgroup.normalizer (R' : Set P),
            ∀ i, q • a i = b i := by
      subst R'
      simpa only [SP,
        FiveTransitive.Degree24.sylowFixedPoints,
        FiveTransitive.Degree24.sylowInNormalizer,
        FiveTransitive.Degree24.sylowNormalizer] using
        (FiveTransitive.LargePrimeNormalizer.sylowNormalizer_transitive_on_fixedPoints
          X P hdegree h5 (k := 5) (by norm_num) s hs S)
    change
      ∀ a b : Fin 5 →
          MulAction.fixedPoints
            (R.subgroupOf (Subgroup.normalizer (R : Set P))) X,
        Function.Injective a → Function.Injective b →
        ∃ q : Subgroup.normalizer (R : Set P),
          ∀ i, q • a i = b i
    exact htransport R (by simpa only [SP, R] using hRSP)
  have hJfive :
      ∀ a b : Fin 5 → F, Function.Injective a →
        Function.Injective b → ∃ q : J, ∀ i, q • a i = b i := by
    intro a b ha hb
    obtain ⟨q, hq⟩ := hNfive a b ha hb
    let qJ : J := ⟨MulAction.toPermHom N F q, ⟨q, rfl⟩⟩
    refine ⟨qJ, ?_⟩
    intro i
    exact hq i
  exact
    FiveTransitive.SmallDegreeFixedAction.alternatingGroup_le_of_card_le_twentySeven_away_mathieu
      F J hfixedFive hfixedUpper hfixedNotTwelve
        hfixedNotTwentyFour hJfive

theorem alternatingGroup_le_of_order_three_support_le_eighteen
    {X : Type} [Fintype X] [DecidableEq X]
    (hX : Fintype.card X = 28)
    (P : Subgroup (Equiv.Perm X))
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b → ∃ q : P, ∀ i, q • a i = b i)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 3 (fixingSubgroup P s))
    (hScard : Nat.card S = 3)
    (g : Equiv.Perm X) (hgP : g ∈ P)
    (hgOrder : orderOf g = 3)
    (hgSupport : g.support.card ≤ 18) :
    alternatingGroup X ≤ P := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hgNe : g ≠ 1 := by
    intro hgOne
    rw [hgOne, orderOf_one] at hgOrder
    omega
  have hcyclePos : 0 < g.cycleType.card :=
    Equiv.Perm.card_cycleType_pos.mpr hgNe
  have hgPrime : Nat.Prime (orderOf g) := by
    rw [hgOrder]
    norm_num
  obtain ⟨m, hm⟩ := Equiv.Perm.cycleType_prime_order hgPrime
  have hgSupportEq : g.support.card = 3 * g.cycleType.card := by
    rw [← g.sum_cycleType, hm, hgOrder]
    simp [Nat.mul_comm]
    omega
  have hfixedCard :
      Fintype.card (Function.fixedPoints g) = 28 - g.support.card := by
    rw [Equiv.Perm.card_fixedPoints, g.sum_cycleType, hX]
  have hfixedFive : 5 ≤ Fintype.card (Function.fixedPoints g) := by
    omega
  have hfixedUpper : Fintype.card (Function.fixedPoints g) ≤ 27 := by
    omega
  have hfixedNotTwelve :
      Fintype.card (Function.fixedPoints g) ≠ 12 := by
    intro h
    omega
  have hfixedNotTwentyFour :
      Fintype.card (Function.fixedPoints g) ≠ 24 := by
    intro h
    omega

  have hcomplCard : g.supportᶜ.card = 28 - g.support.card := by
    rw [Finset.card_compl, hX]
  have hfiveCompl : 5 ≤ g.supportᶜ.card := by
    rw [hcomplCard]
    omega
  obtain ⟨tFin, htSub, htCard⟩ :=
    Finset.exists_subset_card_eq hfiveCompl
  let t : Set X := (tFin : Set X)
  have ht : t.ncard = 5 := by
    simpa only [t, Set.ncard_coe_finset] using htCard
  let r : P := ⟨g, hgP⟩
  have hrFix : ∀ x ∈ t, r • x = x := by
    intro x hxt
    change x ∈ tFin at hxt
    have hxCompl : x ∈ g.supportᶜ := htSub hxt
    rw [Finset.mem_compl] at hxCompl
    change g x = x
    simpa only [Equiv.Perm.mem_support, not_not] using hxCompl
  let Ht : Subgroup P := fixingSubgroup P t
  let rT : Ht := ⟨r, (mem_fixingSubgroup_iff P).mpr hrFix⟩
  have hrOrder : orderOf r = 3 := by
    calc
      orderOf r = orderOf (r : Equiv.Perm X) :=
        (Subgroup.orderOf_coe r).symm
      _ = orderOf g := by rfl
      _ = 3 := hgOrder
  have hrTOrder : orderOf rT = 3 := by
    calc
      orderOf rT = orderOf (rT : P) :=
        (Subgroup.orderOf_coe rT).symm
      _ = orderOf r := by rfl
      _ = 3 := hrOrder
  let R : Subgroup Ht := Subgroup.zpowers rT
  have hRcard : Nat.card R = 3 := by
    rw [Nat.card_zpowers, hrTOrder]
  have hRisP : IsPGroup 3 R := by
    apply IsPGroup.of_card
    rw [hRcard, pow_one]
  obtain ⟨T, hRleT⟩ := hRisP.exists_le_sylow
  have hstabilizerCard :
      Nat.card (fixingSubgroup P s) = Nat.card Ht := by
    simpa only [Ht] using
      Degree28BlockEscape.five_stabilizer_card_eq X P h5 s t hs ht
  have hTcard : Nat.card T = 3 := by
    calc
      Nat.card T =
          3 ^ (Nat.card Ht).factorization 3 := T.card_eq_multiplicity
      _ = 3 ^ (Nat.card (fixingSubgroup P s)).factorization 3 := by
        rw [hstabilizerCard]
      _ = Nat.card S := S.card_eq_multiplicity.symm
      _ = 3 := hScard
  have hReq : R = (T : Subgroup Ht) := by
    apply Subgroup.eq_of_le_of_card_ge hRleT
    rw [hRcard, hTcard]
  have hRSP :
      FiveTransitive.PrimeCyclicFixedAction.cyclicSubgroup P r =
        FiveTransitive.Degree24.sylowImage X P t T := by
    change Subgroup.zpowers r = (T : Subgroup Ht).map Ht.subtype
    calc
      Subgroup.zpowers r =
          (Subgroup.zpowers rT).map Ht.subtype := by
        symm
        rw [MonoidHom.map_zpowers]
        rfl
      _ = (T : Subgroup Ht).map Ht.subtype := by
        exact congrArg (Subgroup.map Ht.subtype) hReq

  let F := FiveTransitive.PrimeCyclicFixedAction.cyclicFixedPoints X P r
  let FC := FiveTransitive.PrimeCyclicFixedAction.cyclicComplement X P r
  letI : Fintype F := Fintype.ofFinite F
  letI : Fintype FC := Fintype.ofFinite FC
  have hFcard :
      Fintype.card F = Fintype.card (Function.fixedPoints g) := by
    exact Fintype.card_congr
      (Degree28BlockEscape.cyclicFixedEquivGeneratorFixed P r)
  have hFfive : 5 ≤ Fintype.card F := by
    rw [hFcard]
    exact hfixedFive
  have hFupper : Fintype.card F ≤ 27 := by
    rw [hFcard]
    exact hfixedUpper
  have hFnotTwelve : Fintype.card F ≠ 12 := by
    rw [hFcard]
    exact hfixedNotTwelve
  have hFnotTwentyFour : Fintype.card F ≠ 24 := by
    rw [hFcard]
    exact hfixedNotTwentyFour
  have hAltFixed :
      alternatingGroup F ≤
        (MulAction.toPermHom
          (FiveTransitive.PrimeCyclicFixedAction.cyclicNormalizer P r) F).range :=
    alternatingGroup_le_cyclic_fixed_range P (by omega) h5 t ht T r hRSP
      hFfive hFupper hFnotTwelve hFnotTwentyFour

  let c : Equiv.Perm FC :=
    FiveTransitive.PrimeCyclicFixedAction.complementPerm X P r
  have hcOrder : orderOf c = 3 := by
    exact FiveTransitive.PrimeCyclicFixedAction.orderOf_complementPerm
      X P r (by norm_num) hrOrder
  have hcPrime : Nat.Prime (orderOf c) := by
    rw [hcOrder]
    norm_num
  obtain ⟨q, hq⟩ := Equiv.Perm.cycleType_prime_order hcPrime
  have hcSupport : c.support = Finset.univ := by
    ext x
    simp only [Equiv.Perm.mem_support, Finset.mem_univ, iff_true]
    exact FiveTransitive.PrimeCyclicFixedAction.complementPerm_fixedPointFree
      X P r x
  have hFCshape : Fintype.card FC = 3 * c.cycleType.card := by
    calc
      Fintype.card FC = c.support.card := by
        rw [hcSupport, Finset.card_univ]
      _ = c.cycleType.sum := c.sum_cycleType.symm
      _ = 3 * c.cycleType.card := by
        rw [hq, hcOrder]
        simp [Nat.mul_comm]
        omega
  have hFCcard : Fintype.card FC = g.support.card := by
    simpa only [FC, r, Fintype.card_coe] using
      Fintype.card_congr
        (Degree28BlockEscape.cyclicComplementEquivSupport P r)
  have hcycleEq : c.cycleType.card = g.cycleType.card := by
    omega
  have hdiagonal :=
    Degree28DiagonalEscape.degree28_fixed_points_exceed_cycle_count
      hX hgOrder hgSupport
  have hcycles : c.cycleType.card < Fintype.card F := by
    rw [hcycleEq, hFcard]
    exact hdiagonal
  exact
    FiveTransitive.PrimeCyclicFixedAction.alternatingGroup_le_of_prime_cyclic_fixed_action_cycle_count
      X P (by omega) h5 r (by norm_num) hrOrder hFfive hAltFixed hcycles

end FiveTransitive.Degree28WitnessClosure

end CFSG
