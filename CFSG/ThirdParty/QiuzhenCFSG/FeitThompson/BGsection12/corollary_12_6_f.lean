module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.corollary_12_6_e

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Corollary 12.6(f). -/
public theorem CFSG.corollary_12_6_f
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E) :
    ∀ Mstar : Subgroup G, Mstar ∈ section9MaximalSubgroups G →
      section12NotConjugate Mstar M →
        section10Msigma M ⊓ section10Msigma Mstar = ⊥ ∧
          Disjoint (section10SigmaPrimes M) (section10SigmaPrimes Mstar) := by
  classical
  intro Mstar hMstar hnotconj
  have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
    section12_rankTwo_of_EData hE hA
  have hnil : Group.IsNilpotent (section10Msigma M) :=
    theorem_12_5_a hM hp hA_M
  rcases lemma_10_12_b (G := G) (M := M) (H := Mstar) hM hMstar hnotconj hnil with
    ⟨hdis, hσdis⟩
  exact ⟨hdis.eq_bot, hσdis⟩


end Section12
