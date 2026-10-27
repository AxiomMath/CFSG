module

public import CFSG.ClassicalGroups.Orthogonal.ElementaryGroupIrreducible
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open scoped Matrix

theorem submodule_eq_bot_or_top_of_statedOmega_quadPlus
    {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (hm : 3 ≤ m)
    (W : Submodule K (Fin m ⊕ Fin m → K))
    (hW : ∀ g ∈ StatedOmega (StatedQuadPlus m K), ∀ w ∈ W,
      (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  let Q : QuadraticForm K (Fin m ⊕ Fin m → K) := quadPlus m K
  let Q₀ : (Fin m ⊕ Fin m → K) → K := StatedQuadPlus m K
  have hQ : ⇑Q = Q₀ := coe_quadPlus m K
  have hE : ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆ = elementaryGroup Q :=
    commutator_orthogonalGroup_quadPlus (K := K) hm
  have hP : ∃ P : Fin 2 → HypPair Q, ∀ i j, i ≠ j → (P i).Orth (P j) :=
    ⟨fun i => plusPair K (Fin.castLE (by omega : 2 ≤ m) i), by
      intro i j hij
      exact plusPair_orth (fun h => hij (Fin.castLE_injective _ h))⟩
  have hW' : ∀ g ∈ elementaryGroup Q, ∀ w ∈ W, g w ∈ W := by
    intro g hg w hw
    let A : StatedOmega Q₀ := (statedOmegaEquiv hQ hE).symm ⟨g, hg⟩
    have hmem : ((A : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ w ∈ W :=
      hW A A.2 w hw
    have hcoe : ((statedOmegaEquiv hQ hE A : elementaryGroup Q) :
        (Fin m ⊕ Fin m → K) ≃ₗ[K] (Fin m ⊕ Fin m → K)) = g := by
      simp [A]
    have hval : ((A : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ w = g w := by
      have h1 : ((statedOmegaEquiv hQ hE A : elementaryGroup Q) :
          (Fin m ⊕ Fin m → K) ≃ₗ[K] (Fin m ⊕ Fin m → K)) w = g w := by
        rw [hcoe]
      rw [coe_statedOmegaEquiv] at h1
      rw [← h1, toLinEquiv_apply]
    rwa [hval] at hmem
  exact submodule_eq_bot_or_top_of_elementaryGroup_invariant
    (Q := Q) (nondegenerate_polarBilin_quadPlus m K) hP W hW'

end CFSG.RankThree.GF2n.Stroth80
