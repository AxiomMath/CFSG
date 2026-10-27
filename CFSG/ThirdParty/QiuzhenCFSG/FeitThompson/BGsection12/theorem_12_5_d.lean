module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.theorem_12_5_c

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Theorem 12.5(d). -/
public theorem CFSG.theorem_12_5_d
    {M A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M) :
    subgroupCentralizerIn (section10Msigma M) A = ⊥ := by
  classical
  obtain ⟨A₀, P, _hA₀, h11⟩ :=
    section12_exists_section11Data_of_tau2_pre hM hp hA
  exact corollary_11_6_b h11


end Section12
