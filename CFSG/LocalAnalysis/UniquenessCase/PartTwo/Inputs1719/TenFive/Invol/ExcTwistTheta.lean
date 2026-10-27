module

public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningSemilinear

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups

variable
  {k : Type} [Field k]

theorem diagramMap_conj_pinnedX_single (t : TwistTag) (i : Fin t.tag.rank) (c : k) :
    diagramMap t k * pinnedX t.tag k (Pi.single i 1) c * (diagramMap t k)⁻¹ =
      pinnedX t.tag k (Pi.single (t.perm i) 1) c := by
  rw [pinnedX_single, pinnedX_single, diagramMap_mul_xUnit_mul_inv]

theorem twistMatrix_conj_pinnedX (t : TwistTag) (l : List (Fin t.tag.rank))
    {γ : Fin t.tag.rank → ℤ} (hγ : IsRoot t.tag γ) :
    ∃ s : k, s * s = 1 ∧ ∀ c : k, (wordWeylMatrix t.tag k l * diagramMap t k) *
      pinnedX t.tag k γ c * (wordWeylMatrix t.tag k l * diagramMap t k)⁻¹ =
      pinnedX t.tag k (ToralSign.wordElt t.tag l • permLattice t.perm γ) (s * c) := by
  obtain ⟨ε, hε, hP⟩ := diagramMap_conj_pinnedX (K := k) t hγ
  obtain ⟨ε', hε', hN⟩ := wordWeylMatrix_conj_pinnedX (k := k) l (hγ.permLattice t.cartan_perm)
  refine ⟨ε' * ε, by linear_combination (ε' * ε') * hε + hε', fun c => ?_⟩
  calc (wordWeylMatrix t.tag k l * diagramMap t k) * pinnedX t.tag k γ c *
        (wordWeylMatrix t.tag k l * diagramMap t k)⁻¹ =
      wordWeylMatrix t.tag k l * (diagramMap t k * pinnedX t.tag k γ c * (diagramMap t k)⁻¹) *
        (wordWeylMatrix t.tag k l)⁻¹ := by group
    _ = _ := by rw [hP, hN, mul_assoc]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
