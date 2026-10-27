module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.theorem_12_5_e

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Theorem 12.5(f). -/
public theorem CFSG.theorem_12_5_f
    {M A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M) :
    ∃ A₁ : Subgroup G, A₁ ∈ section10PrimeOrderSubgroupsIn p A ∧
      subgroupCentralizerIn (section10Msigma M) A₁ = ⊥ := by
  classical
  obtain ⟨A₀, P, _hA₀, h11⟩ :=
    section12_exists_section11Data_of_tau2_pre hM hp hA
  rcases corollary_11_6_c h11 with
    ⟨A₁, A₂, hA₁, _hA₂, _hne, hC₁, _hC₂⟩
  exact ⟨A₁, hA₁, hC₁⟩


end Section12
