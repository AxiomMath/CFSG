module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.lemma_12_1_f

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# lemma_12_1_g
-/

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Lemma 12.1(g). -/
public theorem CFSG.lemma_12_1_g
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (_hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p M) :
    A ∈ maximalElementaryAbelianSubgroups p.val G ∧
      p ∉ section12BetaPrimesOfGroup G := by
  rcases (by simpa [section12Tau2Primes] using hp) with ⟨hpσ, hprank⟩
  rcases (by simpa [section12RankTwoElementaryAbelianIn] using hA) with ⟨hAM, hArank⟩
  have hpα : p ∉ section10AlphaPrimes M := by
    intro hpα
    exact hpσ (section12_sigmaPrimes_mem_of_alphaPrimes_mem hM hpα)
  exact ⟨(lemma_10_4_c (G := G) hM hpσ hprank).2 hAM hArank,
    by simpa [section12BetaPrimesOfGroup] using
      (lemma_10_4_c (G := G) hM hpσ hprank).1⟩

end Section12
