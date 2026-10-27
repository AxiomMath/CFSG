module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.proposition_12_4_b

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

public theorem CFSG.section12_exists_primeOrder_unique_normalizer_of_tau2_pre
    {M A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M) :
    ∃ A₀ : Subgroup G, A₀ ∈ section10PrimeOrderSubgroupsIn p A ∧
      section9MaximalSubgroupsContaining (Subgroup.normalizer (A₀ : Set G)) = {M} := by
  classical
  rcases (by simpa [section12Tau2Primes] using hp) with ⟨hpσ, _hprank⟩
  by_contra hnone
  have hnotUnique :
      ∀ A₀ : Subgroup G, A₀ ∈ section10PrimeOrderSubgroupsIn p A →
        section9MaximalSubgroupsContaining (Subgroup.normalizer (A₀ : Set G)) ≠ {M} := by
    intro A₀ hA₀ huniq
    exact hnone ⟨A₀, hA₀, huniq⟩
  exact hpσ (proposition_12_4_b hM hA hnotUnique).1

public theorem CFSG.section12_exists_section11Data_of_tau2_pre
    {M A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M) :
    ∃ A₀ : Subgroup G, ∃ P : Sylow p.val M,
      A₀ ∈ section10PrimeOrderSubgroupsIn p A ∧ section11Data M A₀ A p P := by
  classical
  rcases (by simpa [section12Tau2Primes] using hp) with ⟨hpσ, _hprank⟩
  rcases section12_exists_primeOrder_unique_normalizer_of_tau2_pre hM hp hA with
    ⟨A₀, hA₀, huniq⟩
  have hMcont :
      M ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (A₀ : Set G)) := by
    rw [huniq]
    simp
  obtain ⟨P, h11⟩ :=
    section12_exists_section11Data_of_not_sigma_pre hM hpσ hA hA₀ hMcont.2
  exact ⟨A₀, P, hA₀, h11⟩

/-- Theorem 12.5(a). -/
public theorem CFSG.theorem_12_5_a
    {M A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M) :
    Group.IsNilpotent (section10Msigma M) := by
  classical
  rcases (by simpa [section12Tau2Primes] using hp) with ⟨hpσ, _hprank⟩
  rcases section12_exists_primeOrder_unique_normalizer_of_tau2_pre hM hp hA with
    ⟨A₀, hA₀, huniq⟩
  have hMcont :
      M ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (A₀ : Set G)) := by
    rw [huniq]
    simp
  obtain ⟨P, h11⟩ :=
    section12_exists_section11Data_of_not_sigma_pre hM hpσ hA hA₀ hMcont.2
  exact theorem_11_3 h11


end Section12
