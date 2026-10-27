module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.lemma_12_8_a

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

/-- Lemma 12.8(c). -/
public theorem CFSG.lemma_12_8_c
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes} {S : Sylow p.val G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hAS : A ≤ (S : Subgroup G)) (hScomm : IsMulCommutative (S : Subgroup G)) :
    (S : Subgroup G) ≤ ambientDerivedSubgroup (Subgroup.normalizer ((S : Subgroup G) : Set G)) ∧
      ambientDerivedSubgroup (Subgroup.normalizer ((S : Subgroup G) : Set G)) ≤
        section8FittingSubgroup E ∧
      section8FittingSubgroup E ≤ Subgroup.centralizer ((S : Subgroup G) : Set G) ∧
      Subgroup.centralizer ((S : Subgroup G) : Set G) ≤ E := by
  exact
    section12_lemma_12_8_c_core_pre
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) (S := S)
      hM hE hp hA hAS hScomm


end Section12
