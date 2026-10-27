module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.corollary_12_10_e

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# lemma_12_11_a
-/

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

private theorem CFSG.section12_not_tau2_of_normalizer_rankTwo_le
    {M A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M)
    (hNormA : Subgroup.normalizer (A : Set G) ≤ M) :
    p ∉ section12Tau2Primes M := by
  classical
  intro hpτ
  rcases theorem_12_5_b (G := G) (M := M) (A := A) (p := p)
      hM hpτ hA with
    ⟨_hSylowAb, hOmega⟩
  have hAsub_p : IsPGroup p.val (A.subgroupOf M) :=
    section12_rankTwo_subgroupOf_isPGroup hA
  obtain ⟨P, hA_le_P⟩ :=
    IsPGroup.exists_le_sylow (G := M) (p := p.val) hAsub_p
  have hA_le_Pamb : A ≤ section10AmbientSylowSubgroup M P := by
    intro a ha
    have haM : a ∈ M := section12_rankTwo_le hA ha
    exact Subgroup.mem_map.mpr
      ⟨⟨a, haM⟩, hA_le_P (by simpa [Subgroup.mem_subgroupOf] using ha), rfl⟩
  rcases hOmega P hA_le_Pamb with ⟨hOmega_eq, hNormP_not⟩
  have hNormP_le_NormA :
      Subgroup.normalizer ((section10AmbientSylowSubgroup M P : Subgroup G) : Set G) ≤
        Subgroup.normalizer (A : Set G) := by
    have hΩchar :
        (omega₁ (G := section10AmbientSylowSubgroup M P) (p := p.val)).Characteristic :=
      omega₁_characteristic (G := section10AmbientSylowSubgroup M P) (p := p.val)
    have hleΩ :
        Subgroup.normalizer ((section10AmbientSylowSubgroup M P : Subgroup G) : Set G) ≤
          Subgroup.normalizer
            (((omega₁ (G := section10AmbientSylowSubgroup M P) (p := p.val)).map
              (section10AmbientSylowSubgroup M P).subtype : Subgroup G) : Set G) :=
      section8_normalizer_map_subtype_le_of_characteristic
        (H := section10AmbientSylowSubgroup M P)
        (K := omega₁ (G := section10AmbientSylowSubgroup M P) (p := p.val))
    have hΩset_eq :
        (((omega₁ (G := section10AmbientSylowSubgroup M P) (p := p.val)).map
          (section10AmbientSylowSubgroup M P).subtype : Subgroup G) : Set G) = (A : Set G) := by
      simpa [section12OmegaOneSubgroup] using
        congrArg (fun K : Subgroup G => (K : Set G)) hOmega_eq
    simpa [hΩset_eq] using hleΩ
  exact hNormP_not (hNormP_le_NormA.trans hNormA)

/-- Lemma 12.11(a). -/
public theorem CFSG.lemma_12_11_a
    {M E E₁₂ E₁ E₂ E₃ A Mstar : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hMstar : Mstar ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (A : Set G))) :
    section12Tau2Primes M ⊆
      {q | q ∈ section10SigmaPrimes Mstar ∧ q ∉ section10BetaPrimes Mstar} := by
  classical
  have hAnormE : section10NormalIn A E :=
    (corollary_12_6_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA).1
  have hE_le_normA : E ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAnormE.1).1 hAnormE.2
  have hE_le_Mstar : E ≤ Mstar := hE_le_normA.trans hMstar.2
  have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
    section12_rankTwo_of_EData hE hA
  have hA_Mstar : A ∈ section12RankTwoElementaryAbelianIn p Mstar :=
    section12_rankTwo_mono hA hE_le_Mstar
  have hp_not_tau2_star : p ∉ section12Tau2Primes Mstar :=
    section12_not_tau2_of_normalizer_rankTwo_le
      (G := G) (M := Mstar) (A := A) (p := p) hMstar.1 hA_Mstar hMstar.2
  have hAp : IsPGroup p.val A := by
    have hElem := (section12_rankTwo_elementary hA).2
    haveI : IsElementaryAbelian p.val A := hElem
    exact IsElementaryAbelian.isPGroup p.val A
  have hp_alt :
      p ∈ section10SigmaPrimes Mstar ∪ section12Tau2Primes Mstar :=
    lemma_12_2_a (G := G) (M := M) (Mstar := Mstar) (X := A) (p := p)
      hM hAp (section12_rankTwo_ne_bot hA) (section12_rankTwo_le hA_M) hMstar
  have hpσstar : p ∈ section10SigmaPrimes Mstar := by
    rcases hp_alt with hpσstar | hpτstar
    · exact hpσstar
    · exact False.elim (hp_not_tau2_star hpτstar)
  have hA_le_msigma_star : A ≤ section10Msigma Mstar :=
    section12_rankTwo_le_msigma_of_sigma
      (G := G) (M := Mstar) (A := A) (p := p) hMstar.1 hpσstar hA_Mstar
  intro q hq
  have hq_data :
      ∃ B : Subgroup G,
        B ∈ section12RankTwoElementaryAbelianIn q E ∧
          B ≤ Mstar ∧ A ≤ Subgroup.centralizer (B : Set G) := by
    by_cases hqp : q = p
    · subst q
      refine ⟨A, hA, (section12_rankTwo_le hA).trans hE_le_Mstar, ?_⟩
      have hElem := (section12_rankTwo_elementary hA).2
      haveI : IsElementaryAbelian p.val A := hElem
      have hAcomm : IsMulCommutative A := hElem.toIsMulCommutative
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (setLike_mul_comm
        (s := A) hx hy).symm
    · obtain ⟨B, hB⟩ :=
        section12_exists_rankTwo_in_E_of_tau2
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
          (E₂ := E₂) (E₃ := E₃) hM hE hq
      have hBnormE : section10NormalIn B E :=
        (corollary_12_6_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := B) (p := q)
          hM hE hq hB).1
      have hpq : p ≠ q := fun hpq => hqp hpq.symm
      have hAcentB : A ≤ Subgroup.centralizer (B : Set G) :=
        section12_normal_rankTwo_centralizes_of_ne
          (G := G) (E := E) (A := A) (B := B) (p := p) (q := q)
          hpq hA hB hAnormE hBnormE
      exact ⟨B, hB, (section12_rankTwo_le hB).trans hE_le_Mstar, hAcentB⟩
  rcases hq_data with ⟨B, hB, hB_le_Mstar, hAcentB⟩
  have hB_M : B ∈ section12RankTwoElementaryAbelianIn q M :=
    section12_rankTwo_of_EData hE hB
  have hB_Mstar : B ∈ section12RankTwoElementaryAbelianIn q Mstar :=
    section12_rankTwo_mono hB hE_le_Mstar
  have hq_not_tau2_star : q ∉ section12Tau2Primes Mstar := by
    intro hqτstar
    have hCbot :
        subgroupCentralizerIn (section10Msigma Mstar) B = ⊥ :=
      theorem_12_5_d (G := G) (M := Mstar) (A := B) (p := q)
        hMstar.1 hqτstar hB_Mstar
    have hA_le_C : A ≤ subgroupCentralizerIn (section10Msigma Mstar) B := by
      intro x hx
      exact ⟨hA_le_msigma_star hx, hAcentB hx⟩
    have hA_bot : A = ⊥ := by
      apply le_bot_iff.mp
      rw [← hCbot]
      exact hA_le_C
    exact (section12_rankTwo_ne_bot hA) hA_bot
  have hqσstar : q ∈ section10SigmaPrimes Mstar := by
    by_contra hq_not_sigma
    have hrank_ge : 2 ≤ primeRank q.val Mstar :=
      section12_primeRank_at_least_two_of_rankTwo hB_Mstar
    have hrank_le : primeRank q.val Mstar ≤ 2 := by
      by_contra hnot_le
      have hgt : 2 < primeRank q.val Mstar := by omega
      have hqMstar : q ∈ subgroupPrimeSet Mstar :=
        section12_rankTwo_prime_mem hB_Mstar
      exact hq_not_sigma
        (section12_sigmaPrimes_mem_of_alphaPrimes_mem hMstar.1 ⟨hqMstar, hgt⟩)
    have hrank_eq : primeRank q.val Mstar = 2 := le_antisymm hrank_le hrank_ge
    exact hq_not_tau2_star (by simpa [section12Tau2Primes] using ⟨hq_not_sigma, hrank_eq⟩)
  have hq_not_betaG : q ∉ section12BetaPrimesOfGroup G :=
    (lemma_12_1_g (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := B) (p := q)
      hM hE hq hB_M).2
  have hq_not_beta_star : q ∉ section10BetaPrimes Mstar := by
    intro hqβ
    have hqIdeal : section10IdealPrime q G := by
      rcases (by simpa [section10BetaPrimes] using hqβ) with ⟨_hqα, hqIdeal⟩
      exact hqIdeal
    exact hq_not_betaG (by simpa [section12BetaPrimesOfGroup] using hqIdeal)
  exact ⟨hqσstar, hq_not_beta_star⟩

end Section12
