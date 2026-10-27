module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.corollary_12_6_a

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Corollary 12.6(b). -/
public theorem CFSG.corollary_12_6_b
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E) :
    Subgroup.centralizer (A : Set G) ≤ subgroupNormalizerIn M (A : Set G) ∧
      subgroupNormalizerIn M (A : Set G) = E ∧
        ¬ Subgroup.normalizer (A : Set G) ≤ M := by
  classical
  have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
    section12_rankTwo_of_EData hE hA
  obtain ⟨A₀, P, _hA₀, h11⟩ :=
    section12_exists_section11Data_of_tau2_pre hM hp hA_M
  rcases h11 with
    ⟨_h11hyp, _hprank, _hideal, _hA₀A, _hAM, _hArank, _hAP, _hPnorm,
      _hCentA₀M, _hCentA_le_CentA₀, hCentAM, _hAmaxRank⟩
  have hCent_le_normIn :
      Subgroup.centralizer (A : Set G) ≤ subgroupNormalizerIn M (A : Set G) := by
    intro x hx
    exact ⟨centralizer_le_normalizer A hx, hCentAM hx⟩
  have hAnorm : section10NormalIn A E :=
    (corollary_12_6_a hM hE hp hA).1
  exact ⟨hCent_le_normIn,
    section12_normalizerIn_rankTwo_eq_complement_pre hM hE hp hA hAnorm,
    section12_not_normalizer_rankTwo_le_M_pre hM hE hp hA⟩


end Section12
