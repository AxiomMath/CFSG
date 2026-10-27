module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.theorem_12_5_a

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Theorem 12.5(b). -/
public theorem CFSG.theorem_12_5_b
    {M A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M) :
    section12HasAbelianSylowSubgroups p M ∧
      ∀ P : Sylow p.val M, A ≤ section10AmbientSylowSubgroup M P →
        section12OmegaOneSubgroup p (section10AmbientSylowSubgroup M P) = A ∧
          ¬ Subgroup.normalizer
              ((section10AmbientSylowSubgroup M P : Subgroup G) : Set G) ≤ M := by
  classical
  rcases (by simpa [section12Tau2Primes] using hp) with ⟨hpσ, _hprank⟩
  rcases section12_exists_primeOrder_unique_normalizer_of_tau2_pre hM hp hA with
    ⟨A₀, hA₀, huniq⟩
  have hMcont :
      M ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (A₀ : Set G)) := by
    rw [huniq]
    simp
  obtain ⟨P₀, h11⟩ :=
    section12_exists_section11Data_of_not_sigma_pre hM hpσ hA hA₀ hMcont.2
  refine ⟨theorem_11_5 h11, ?_⟩
  intro P hAP
  have hpM : p ∈ subgroupPrimeSet M :=
    section12_rankTwo_prime_mem hA
  have hPnorm_not :
      ¬ Subgroup.normalizer
          ((section10AmbientSylowSubgroup M P : Subgroup G) : Set G) ≤ M := by
    intro hPnorm
    exact hpσ ⟨hpM, P, hPnorm⟩
  have h11P : section11Data M A₀ A p P := by
    rcases h11 with
      ⟨h11hyp, hprank, hideal, hA₀A, hAM, hArank, _hAP₀, _hP₀norm,
        hCentA₀M, hCentA_le_CentA₀, hCentAM, hAmaxRank⟩
    exact ⟨h11hyp, hprank, hideal, hA₀A, hAM, hArank, hAP, hPnorm_not,
      hCentA₀M, hCentA_le_CentA₀, hCentAM, hAmaxRank⟩
  refine ⟨?_, hPnorm_not⟩
  simpa [section11OmegaOne, section12OmegaOneSubgroup] using
    (corollary_11_6_a h11P).symm


end Section12
