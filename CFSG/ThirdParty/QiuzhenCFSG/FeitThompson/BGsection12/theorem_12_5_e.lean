module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.theorem_12_5_d

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Theorem 12.5(e). -/
public theorem CFSG.theorem_12_5_e
    {M A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M) :
    ∀ Mstar : Subgroup G, Mstar ∈ section9MaximalSubgroupsContaining A → Mstar ≠ M →
      section10Msigma M ⊓ Mstar = ⊥ := by
  classical
  rcases (by simpa [section12Tau2Primes] using hp) with ⟨hpσ, _hprank⟩
  intro Mstar hMstar hMstar_ne
  let K : Subgroup G := section10Msigma M ⊓ Mstar
  change K = ⊥
  have hAinf : A ∈ section12RankTwoElementaryAbelianIn p (M ⊓ Mstar) :=
    ⟨le_inf (section12_rankTwo_le hA) hMstar.2, section12_rankTwo_elementary hA⟩
  by_cases hExists :
      ∃ A₀ : Subgroup G, A₀ ∈ section10PrimeOrderSubgroupsIn p A ∧
        Subgroup.normalizer (A₀ : Set G) ≤ Mstar
  · rcases hExists with ⟨A₀, hA₀, hNA₀⟩
    have hcent : A ≤ Subgroup.centralizer (K : Set G) := by
      simpa [K] using
        lemma_12_3_a (M := M) (Mstar := Mstar) (A := A) (A₀ := A₀) (p := p)
          hM hMstar.1 hMstar_ne hAinf hA₀ hNA₀ hpσ
    have hK_le_C : K ≤ subgroupCentralizerIn (section10Msigma M) A := by
      intro x hxK
      refine ⟨?_, ?_⟩
      · have hxK' : x ∈ section10Msigma M ⊓ Mstar := by
          simpa [K] using hxK
        exact hxK'.1
      · change x ∈ Subgroup.centralizer (A : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        exact (Subgroup.mem_centralizer_iff.mp (hcent ha) x hxK).symm
    exact le_bot_iff.mp (by
      rw [← theorem_12_5_d hM hp hA]
      exact hK_le_C)
  · have hnotUniqueStar :
        ∀ X : Subgroup G, X ∈ section10PrimeOrderSubgroupsIn p A →
          section9MaximalSubgroupsContaining (Subgroup.normalizer (X : Set G)) ≠ {Mstar} := by
      intro X hX huniq
      have hMstar_mem :
          Mstar ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (X : Set G)) := by
        rw [huniq]
        simp
      exact hExists ⟨X, hX, hMstar_mem.2⟩
    have hAstar : A ∈ section12RankTwoElementaryAbelianIn p Mstar :=
      section12_rankTwo_of_inf_right_pre hAinf
    rcases proposition_12_4_b hMstar.1 hAstar hnotUniqueStar with
      ⟨hpσstar, _hαstar_bot, hnilStar⟩
    rcases section12_exists_primeOrder_unique_normalizer_of_tau2_pre hM hp hA with
      ⟨A₀, hA₀, huniq⟩
    rcases (by simpa [section10PrimeOrderSubgroupsIn] using hA₀) with
      ⟨hA₀A, hA₀card⟩
    have hA₀p : IsPGroup p.val A₀ := by
      refine IsPGroup.of_card (p := p.val) (G := A₀) (n := 1) ?_
      simpa [pow_one] using hA₀card
    have hA₀ne : A₀ ≠ ⊥ := section12_primeOrder_ne_bot hA₀
    have hA₀Mstar : A₀ ≤ Mstar := hA₀A.trans hMstar.2
    have hMcont :
        M ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (A₀ : Set G)) := by
      rw [huniq]
      simp
    have hnotconj : section12NotConjugate M Mstar :=
      lemma_12_2_b (G := G) (M := Mstar) (Mstar := M) (X := A₀) (p := p)
        hMstar.1 hA₀p hA₀ne hA₀Mstar hMcont
        (Or.inl ⟨hpσstar, hMstar_ne⟩)
    let C : Subgroup G := ⁅K, A⁆
    have hAK : A ≤ Subgroup.normalizer (K : Set G) := by
      simpa [K] using
        section12_rankTwo_le_normalizer_msigma_inf_pre (M := M) (Mstar := Mstar) hAinf
    have hC_le_K : C ≤ K := by
      simp [C, section12_commutator_le_left_of_le_normalizer_pre hAK]
    have hK_le_Msigma : K ≤ section10Msigma M := by
      dsimp [K]
      exact inf_le_left
    have hK_le_Mstar : K ≤ Mstar := by
      dsimp [K]
      exact inf_le_right
    have hC_le_Msigma : C ≤ section10Msigma M := hC_le_K.trans hK_le_Msigma
    have hAσstar : A ≤ section10Msigma Mstar :=
      section12_rankTwo_le_msigma_of_sigma hMstar.1 hpσstar hAstar
    have hσstar_le_Mstar : section10Msigma Mstar ≤ Mstar := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
      exact y.property
    have hσstar_norm : ((section10Msigma Mstar).subgroupOf Mstar).Normal := by
      simpa [section12Msigma_subgroupOf_eq] using
        section10MsigmaSubgroup_normal (M := Mstar)
    have hC_le_sigma_star : C ≤ section10Msigma Mstar := by
      letI : ((section10Msigma Mstar).subgroupOf Mstar).Normal := hσstar_norm
      simpa [C] using
        section12_commutator_le_right_of_normal_subgroupOf_pre
          (M := Mstar) (N := section10Msigma Mstar) (K := K) (A := A)
          hσstar_le_Mstar hK_le_Mstar hAσstar
    have hdis :
        Disjoint (section10Msigma Mstar) (section10Msigma M) :=
      (lemma_10_12_b (G := G) (M := Mstar) (H := M)
        hMstar.1 hM hnotconj hnilStar).1
    have hCbot : C = ⊥ := by
      have hC_le_inf : C ≤ section10Msigma Mstar ⊓ section10Msigma M := by
        intro x hx
        exact ⟨hC_le_sigma_star hx, hC_le_Msigma hx⟩
      exact le_bot_iff.mp (by
        rw [← hdis.eq_bot]
        exact hC_le_inf)
    have hK_le_centA : K ≤ Subgroup.centralizer (A : Set G) := by
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := K) (H₂ := A)).mp
        (by simpa [C] using hCbot)
    have hK_le_C : K ≤ subgroupCentralizerIn (section10Msigma M) A := by
      intro x hxK
      exact ⟨hK_le_Msigma hxK, hK_le_centA hxK⟩
    exact le_bot_iff.mp (by
      rw [← theorem_12_5_d hM hp hA]
      exact hK_le_C)


end Section12
