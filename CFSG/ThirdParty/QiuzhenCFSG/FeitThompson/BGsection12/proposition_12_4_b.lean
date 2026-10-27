module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.proposition_12_4_a

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Proposition 12.4(b). -/
public theorem CFSG.proposition_12_4_b
    {M A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M)
    (hnotUnique :
      ∀ A₀ : Subgroup G, A₀ ∈ section10PrimeOrderSubgroupsIn p A →
        section9MaximalSubgroupsContaining (Subgroup.normalizer (A₀ : Set G)) ≠ {M}) :
    p ∈ section10SigmaPrimes M ∧ section10Malpha M = ⊥ ∧
      Group.IsNilpotent (section10Msigma M) := by
  classical
  have hpσ : p ∈ section10SigmaPrimes M :=
    section12_not_not_sigma_in_prop_12_4_pre hM hA hnotUnique
  have hpα : p ∉ section10AlphaPrimes M :=
    section12_not_alpha_in_prop_12_4_pre hM hpσ hA hnotUnique
  have hαbot : section10Malpha M = ⊥ :=
    section12_malpha_eq_bot_of_sigma_not_alpha_pre hM hpσ hpα hA hnotUnique
  exact ⟨hpσ, hαbot, section12_msigma_nilpotent_of_malpha_eq_bot_pre hM hαbot⟩


end Section12
