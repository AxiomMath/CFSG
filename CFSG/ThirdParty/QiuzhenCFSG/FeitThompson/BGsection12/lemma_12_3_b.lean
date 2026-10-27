module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.lemma_12_3_a

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Lemma 12.3(b). -/
public theorem CFSG.lemma_12_3_b
    {M Mstar A A₀ : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMstar : Mstar ∈ section9MaximalSubgroups G) (hMstar_ne : Mstar ≠ M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p (M ⊓ Mstar))
    (hA₀ : A₀ ∈ section10PrimeOrderSubgroupsIn p A)
    (hNA₀ : Subgroup.normalizer (A₀ : Set G) ≤ Mstar)
    (hp : p ∈ section10SigmaPrimes M) (hpα : p ∉ section10AlphaPrimes M) :
    A ≤ Subgroup.centralizer (section10Malpha M ⊓ Mstar : Set G) := by
  classical
  let K : Subgroup G := section10Malpha M ⊓ Mstar
  let C : Subgroup G := ⁅K, A⁆
  have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
    section12_rankTwo_of_inf_left_pre hA
  have hA_Mstar : A ∈ section12RankTwoElementaryAbelianIn p Mstar :=
    section12_rankTwo_of_inf_right_pre hA
  have hAM : A ≤ M := section12_rankTwo_le hA_M
  have hKleMalpha : K ≤ section10Malpha M := inf_le_left
  have hKleMstar : K ≤ Mstar := inf_le_right
  have hKp' : IsPiSubgroup (G := G) (section10PPrimeSet p) K :=
    section12_isPiSubgroup_pPrime_of_le_malpha_pre hM hpα hKleMalpha
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := by
    simpa [K] using section12_rankTwo_le_normalizer_malpha_inf_pre (M := M) (Mstar := Mstar) hA
  have hC_le_K : C ≤ K := by
    simpa [C] using section12_commutator_le_left_of_le_normalizer_pre hAK
  have hC_le_Malpha : C ≤ section10Malpha M := hC_le_K.trans hKleMalpha
  have hC_le_sigma_star : C ≤ section10Msigma Mstar := by
    by_cases hpσstar : p ∈ section10SigmaPrimes Mstar
    · simpa [C] using
        section12_commutator_le_msigma_of_sigma_rankTwo_pre
          (M := Mstar) (A := A) (K := K) (p := p)
          hMstar hpσstar hA_Mstar hKleMstar
    · simpa [C] using
        section12_commutator_le_msigma_of_not_sigma_rankTwo_pre
          (M := Mstar) (A := A) (A₀ := A₀) (K := K) (p := p)
          hMstar hpσstar hA_Mstar hA₀ hNA₀ hKleMstar hKp' hAK
  rcases (by simpa [section10PrimeOrderSubgroupsIn] using hA₀) with
    ⟨hA₀A, hA₀card⟩
  have hA₀p : IsPGroup p.val A₀ := by
    refine IsPGroup.of_card (p := p.val) (G := A₀) (n := 1) ?_
    simpa [pow_one] using hA₀card
  have hA₀ne : A₀ ≠ ⊥ := by
    intro hbot
    have hcard_bot : Nat.card A₀ = 1 :=
      (Subgroup.card_eq_one (H := A₀)).2 hbot
    have hp_eq_one : p.val = 1 := by
      rw [← hA₀card, hcard_bot]
    exact (ne_of_gt p.2.one_lt) hp_eq_one
  have hA₀M : A₀ ≤ M := hA₀A.trans hAM
  have hMstar_cont :
      Mstar ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (A₀ : Set G)) :=
    ⟨hMstar, hNA₀⟩
  have hM_ne_Mstar : M ≠ Mstar := fun hEq => hMstar_ne hEq.symm
  have hnotconj : section12NotConjugate Mstar M :=
    lemma_12_2_b (G := G) (M := M) (Mstar := Mstar) (X := A₀) (p := p)
      hM hA₀p hA₀ne hA₀M hMstar_cont (Or.inl ⟨hp, hM_ne_Mstar⟩)
  have hdis : Disjoint (section10Malpha M) (section10Msigma Mstar) :=
    (lemma_10_12_a (G := G) (M := M) (H := Mstar)
      hM hMstar hnotconj).1
  have hCbot : C = ⊥ := by
    have hC_le_inf : C ≤ section10Malpha M ⊓ section10Msigma Mstar := by
      intro x hx
      exact ⟨hC_le_Malpha hx, hC_le_sigma_star hx⟩
    exact le_bot_iff.mp (by
      rw [← hdis.eq_bot]
      exact hC_le_inf)
  have hK_le_centA : K ≤ Subgroup.centralizer (A : Set G) := by
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := K) (H₂ := A)).mp
      (by simpa [C] using hCbot)
  exact (Subgroup.le_centralizer_iff (H := K) (K := A)).mp hK_le_centA


end Section12
