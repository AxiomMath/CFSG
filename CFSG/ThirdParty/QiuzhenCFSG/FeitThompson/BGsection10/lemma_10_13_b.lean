module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection10.lemma_10_13_a

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# Lemma 10.13(b) from BG Section 10

This file contains Lemma 10.13(b) from BG Section 10.
-/

section Section10

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Lemma 10.13(b). -/
public theorem CFSG.lemma_10_13_b
    {p : Nat.Primes} {A P A₀ : Subgroup G}
    (hpG : p ∈ subgroupPrimeSet (⊤ : Subgroup G))
    (hA : A ∈ section10RankTwoMaximalElementaryAbelianSubgroups p G)
    (hPp : IsPGroup p.val P) (hPnonab : ¬ IsMulCommutative P) (hAleP : A ≤ P)
    (hA₀ : A₀ ∈ section10PrimeOrderSubgroupsIn p A)
    (hA₀ne : A₀ ≠ section10OmegaOneCenter p P) :
    ∃ Z : Subgroup G,
      section10OmegaOneCenter p P ≤ Z ∧
        IsCyclic Z ∧
        Disjoint A₀ Z ∧
        subgroupCentralizerIn P A = A₀ ⊔ Z := by
  exact
    (section10_lemma_10_13_structural_package
      (G := G) hpG hA hPp hPnonab hAleP hA₀ hA₀ne).2.1

end Section10
