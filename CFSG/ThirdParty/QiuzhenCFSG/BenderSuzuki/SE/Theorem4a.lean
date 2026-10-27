module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section7Final

namespace CFSG
end CFSG
open CFSG

/-!
# Theorem 4(a) from the completed Section 7 argument

The rank-two hypothesis supplies two distinct involutions in the base
stabilizer.  Their conjugacy makes the centralizer index `theorem4bM` larger
than one, while strong embedding makes it odd.  An odd prime divisor therefore
has prime share at least two.  If the conjugate-coset action were not doubly
transitive, Corollary 5.7 would produce a `(6A)` witness and hence a maximal
`(6D)` witness.  Such a witness contradicts the Section 7 proof of Theorem
4(b).  The second theorem is the corresponding transitivity of the base
stabilizer on the complement of the base coset.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

private theorem exists_two_distinct_nontrivial_of_card_four
    {A : Type*} [Group A] [Finite A] (hcard : Nat.card A = 4) :
    ∃ a b : A, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  have hcardF : Fintype.card A = 4 := by
    simpa [Nat.card_eq_fintype_card] using hcard
  have htwo_lt : 2 < Fintype.card A := by omega
  rcases Fintype.two_lt_card_iff.mp htwo_lt with
    ⟨a, b, c, hab, hac, hbc⟩
  by_cases ha : a = 1
  · by_cases hb : b = 1
    · exact False.elim (hab (ha.trans hb.symm))
    · by_cases hc : c = 1
      · exact False.elim (hac (ha.trans hc.symm))
      · exact ⟨b, c, hb, hc, hbc⟩
  · by_cases hb : b = 1
    · by_cases hc : c = 1
      · exact False.elim (hbc (hb.trans hc.symm))
      · exact ⟨a, c, ha, hc, hac⟩
    · exact ⟨a, b, ha, hb, hab⟩

private theorem exists_two_distinct_involutions_in_base
    {X : Type*} [Group X] [Finite X] {M : Subgroup X}
    (hrank : TwoRankAtLeastTwo (involutionCore M)) :
    ∃ z s : X, z ∈ M ∧ IsInvolution z ∧ s ∈ M ∧
      IsInvolution s ∧ z ≠ s := by
  obtain ⟨E, hEcard, hEsq⟩ :=
    TwoRankAtLeastTwo.exists_subgroup hrank
  obtain ⟨a, b, ha, hb, hab⟩ :=
    exists_two_distinct_nontrivial_of_card_four hEcard
  let z : X := (((a : E) : involutionCore M) : M)
  let s : X := (((b : E) : involutionCore M) : M)
  have hzM : z ∈ M := ((a : involutionCore M) : M).property
  have hsM : s ∈ M := ((b : involutionCore M) : M).property
  have hz : IsInvolution z := by
    constructor
    · intro hz1
      apply ha
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact hz1
    · change ((((a : E) : involutionCore M) : M) : X) ^ 2 = 1
      exact congrArg
        (fun x : E => ((((x : E) : involutionCore M) : M) : X))
        (hEsq a)
  have hs : IsInvolution s := by
    constructor
    · intro hs1
      apply hb
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact hs1
    · change ((((b : E) : involutionCore M) : M) : X) ^ 2 = 1
      exact congrArg
        (fun x : E => ((((x : E) : involutionCore M) : M) : X))
        (hEsq b)
  have hzs : z ≠ s := by
    intro h
    apply hab
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact h
  exact ⟨z, s, hzM, hz, hsM, hs, hzs⟩

/-- Rank at least two in the involution core supplies two distinct ambient
involutions in the base subgroup. -/
public theorem exists_two_distinct_involutions_in_involutionCore
    {X : Type*} [Group X] [Finite X] {M : Subgroup X}
    (hrank : TwoRankAtLeastTwo (involutionCore M)) :
    ∃ z s : X, z ∈ M ∧ IsInvolution z ∧ s ∈ M ∧
      IsInvolution s ∧ z ≠ s :=
  exists_two_distinct_involutions_in_base hrank

private theorem exists_involution_one_lt_theorem4bM
    {X : Type*} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M)
    (hrank : TwoRankAtLeastTwo (involutionCore M)) :
    ∃ z : X, IsInvolution z ∧ z ∈ M ∧ 1 < theorem4bM M z := by
  obtain ⟨z, s, hzM, hz, hsM, hs, hzs⟩ :=
    exists_two_distinct_involutions_in_base hrank
  obtain ⟨g, hgM, hzg⟩ :=
    hM.involutions_conjugate_in hzM hz hsM hs
  let C : Subgroup M :=
    (M ⊓ Subgroup.centralizer ({z} : Set X)).subgroupOf M
  have hCne : C ≠ ⊤ := by
    intro hCtop
    have hMC : M ≤ M ⊓ Subgroup.centralizer ({z} : Set X) :=
      Subgroup.subgroupOf_eq_top.mp hCtop
    have hgC : g ∈ Subgroup.centralizer ({z} : Set X) := (hMC hgM).2
    have hcomm : g * z = z * g :=
      Subgroup.mem_centralizer_singleton_iff.mp hgC
    apply hzs
    rw [← hzg, rightConjugateElem]
    symm
    calc
      g⁻¹ * z * g = g⁻¹ * (z * g) := by rw [mul_assoc]
      _ = g⁻¹ * (g * z) := by rw [hcomm]
      _ = z := by simp
  have hindex : 1 < C.index := Subgroup.one_lt_index_of_ne_top hCne
  have hindex' : 1 < theorem4bM M z := by
    change 1 < C.index
    exact hindex
  exact ⟨z, hz, hzM, hindex'⟩

private theorem theorem4bM_odd
    {X : Type*} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) {z : X}
    (hz : IsInvolution z) (hzM : z ∈ M) :
    Odd (theorem4bM M z) := by
  obtain ⟨t, ht, htM⟩ := hM.exists_involution_not_mem
  let D : Subgroup X := M ⊓ rightConjugate M t
  let C : Subgroup D :=
    (D ⊓ Subgroup.centralizer ({t} : Set X)).subgroupOf D
  have hDodd : Odd (Nat.card D) := by
    simpa [D] using hM.inf_rightConjugate_card_odd htM
  have hCindexOdd : Odd C.index :=
    Odd.of_dvd_nat hDodd (Subgroup.index_dvd_card C)
  have hindex : C.index = theorem4bM M z := by
    simpa [C, D] using
      hM.theorem4b_inf_rightConjugate_outside_centralizer_index_eq
        hzM hz ht htM
  simpa [hindex] using hCindexOdd

private theorem exists_odd_prime_share_two_le
    {X : Type*} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M)
    (hrank : TwoRankAtLeastTwo (involutionCore M)) :
    ∃ (z : X) (p : ℕ), IsInvolution z ∧ z ∈ M ∧
      Nat.Prime p ∧ Odd p ∧ 2 ≤ theorem4bPrimeShare M z p := by
  obtain ⟨z, hz, hzM, hmOne⟩ :=
    exists_involution_one_lt_theorem4bM hM hrank
  have hmOdd : Odd (theorem4bM M z) := theorem4bM_odd hM hz hzM
  obtain ⟨p, hp, hpDiv⟩ :=
    Nat.exists_prime_and_dvd (Nat.ne_of_gt hmOne)
  have hpOdd : Odd p := Odd.of_dvd_nat hmOdd hpDiv
  have hmNe : theorem4bM M z ≠ 0 :=
    Nat.ne_of_gt (lt_trans Nat.zero_lt_one hmOne)
  have hfac : 1 ≤ (theorem4bM M z).factorization p :=
    hp.factorization_pos_of_dvd hmNe hpDiv
  have hshare : 2 ≤ theorem4bPrimeShare M z p := by
    calc
      2 ≤ p := hp.two_le
      _ = p ^ 1 := by simp
      _ ≤ p ^ (theorem4bM M z).factorization p :=
        Nat.pow_le_pow_right hp.pos hfac
      _ = theorem4bPrimeShare M z p := by rfl
  exact ⟨z, p, hz, hzM, hp, hpOdd, hshare⟩

private theorem theorem4a_twoTransitive_of_noSixD
    {X : Type*} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hno : ∀ _d : Theorem4bSixD M, False) :
    MulAction.IsMultiplyPretransitive X (conjugateCosetSpace M) 2 := by
  by_contra hnot2
  obtain ⟨z, p, hz, hzM, hp, hpOdd, hshare⟩ :=
    exists_odd_prime_share_two_le hM hrank
  obtain ⟨e, _heq⟩ :=
    exists_theorem4bSixA_card_eq_primeShare_of_not_twoTransitive
      hM hT2 hnot2 hz hzM hp hpOdd hshare
  obtain ⟨d⟩ := exists_theorem4bSixD ⟨e⟩
  exact hno d

private theorem base_stabilizer_transitive_of_twoTransitive
    {X : Type*} [Group X] [Finite X] (M : Subgroup X)
    (htwo : MulAction.IsMultiplyPretransitive X
      (conjugateCosetSpace M) 2) :
    IsTransitiveOn M
      {omega : conjugateCosetSpace M |
        omega ≠ (QuotientGroup.mk 1 : conjugateCosetSpace M)} := by
  change ∀ ⦃alpha beta : conjugateCosetSpace M⦄,
    alpha ≠ (QuotientGroup.mk 1 : conjugateCosetSpace M) →
    beta ≠ (QuotientGroup.mk 1 : conjugateCosetSpace M) →
      ∃ f : M, (f : X) • alpha = beta
  intro alpha beta halpha hbeta
  have htwo' : ∀ {a b c d : conjugateCosetSpace M},
      a ≠ b → c ≠ d → ∃ g : X, g • a = c ∧ g • b = d :=
    MulAction.is_two_pretransitive_iff.mp htwo
  obtain ⟨g, hgbase, hgalpha⟩ := htwo'
    (a := (QuotientGroup.mk 1 : conjugateCosetSpace M))
    (b := alpha)
    (c := (QuotientGroup.mk 1 : conjugateCosetSpace M))
    (d := beta) halpha.symm hbeta.symm
  have hgM : g ∈ M := by
    rw [← baseCoset_stabilizer (X := X) M]
    exact MulAction.mem_stabilizer_iff.mpr hgbase
  exact ⟨⟨g, hgM⟩, by simpa using hgalpha⟩

/-- Theorem 4(a): in the Section 7 minimal-counterexample setting, the
conjugate-coset action is doubly transitive. -/
public theorem IsStronglyEmbedded.theorem4a_twoTransitive_of_section7
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hX : IsSimpleGroup X)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hinduction : ∀ H : Subgroup X, H ≠ ⊤ →
      ∀ N : Subgroup H, IsStronglyEmbedded N →
        TheoremSEConclusion N) :
    MulAction.IsMultiplyPretransitive X (conjugateCosetSpace M) 2 := by
  apply theorem4a_twoTransitive_of_noSixD hM hrank hT2
  intro d
  exact d.data.not_Theorem4bAtBase
    (hM.theorem4bAtBase_of_section7 hX hrank hT2 hinduction)

/-- The base stabilizer form of Theorem 4(a): `M` is transitive on all
nonbase conjugate cosets. -/
public theorem IsStronglyEmbedded.theorem4a_baseStabilizer_transitive_of_section7
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) (hX : IsSimpleGroup X)
    (hrank : TwoRankAtLeastTwo (involutionCore M))
    (hT2 : Theorem4bProposition63Theorem2 M (involutionsSet X))
    (hinduction : ∀ H : Subgroup X, H ≠ ⊤ →
      ∀ N : Subgroup H, IsStronglyEmbedded N →
        TheoremSEConclusion N) :
    IsTransitiveOn M
      {omega : conjugateCosetSpace M |
        omega ≠ (QuotientGroup.mk 1 : conjugateCosetSpace M)} :=
  base_stabilizer_transitive_of_twoTransitive M
    (hM.theorem4a_twoTransitive_of_section7
      hX hrank hT2 hinduction)

end CFSG.BenderSuzuki
