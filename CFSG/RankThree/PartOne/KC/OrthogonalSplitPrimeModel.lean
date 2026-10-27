module

public import CFSG.RankThree.PartOne.KC.OrthogonalSplitPrime
public import CFSG.RankThree.PartOne.KC.OrthogonalQPlusOneModel

public section

open CFSG CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.RankThree.PartOne.KCOrthogonalModel

namespace CFSG.RankThree.PartOne

theorem orthogonal_split_prime_common_centralizer (G : Type) [Group G] (t : StatedLieTag)
    (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) (n ℓ f p : ℕ)
    (h : StatedClassicalModel G t n ℓ f) :
    p.Prime → 3 < p → p ≠ ℓ → p ∣ ℓ ^ f - 1 →
    match t with
    | .POmegaOdd => ∀ (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ f →
        G ≃* StatedProj (StatedOmega (StatedQuadOdd n K)) →
          CommonLayerCentralizerTrivial (matrixProjectiveDerived (coordinateQuadOdd n K)) p
    | .POmegaPlus => ∀ (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ f →
        G ≃* StatedProj (StatedOmega (StatedQuadPlus n K)) →
          CommonLayerCentralizerTrivial (matrixProjectiveDerived (coordinateQuadPlus n K)) p
    | .POmegaMinus => ∀ (hn : 1 ≤ n) (K : Type) [Field K] [Finite K], Nat.card K = ℓ ^ f →
        ∀ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
        G ≃* StatedProj (StatedOmega (StatedQuadMinus n K b c)) →
          CommonLayerCentralizerTrivial
            (matrixProjectiveDerived (coordinateQuadMinus n K hn b c)) p
    | _ => False := by
  intro hp hp3 hpℓ hpq
  rcases ht with rfl | rfl | rfl
  ·
    intro K _ _ hK e D hD A hAH hA hAcard
    obtain ⟨-, hnd, hS3, -⟩ := coordinate_model_witness_odd h K hK e
    refine matrix_model_of_intrinsic (d := 2 * n + 1) (by omega) (coordinateQuadOdd n K) hnd hS3
      (fun D' hD' A' hA' hAc' => ?_) D hD A hAH hA hAcard
    exact ((split_prime_orthogonal_plane_components_generate hnd hS3 hp hp3
      (by rw [hK]; exact hpq) A' hA' hAc').2 D' hD').2
  ·
    intro K _ _ hK e D hD A hAH hA hAcard
    obtain ⟨-, hnd, hS3, -⟩ := coordinate_model_witness_plus h K hK e
    have hn : 1 ≤ n := by
      have := h.1.2.2
      omega
    refine matrix_model_of_intrinsic (d := 2 * n) (by omega) (coordinateQuadPlus n K) hnd hS3
      (fun D' hD' A' hA' hAc' => ?_) D hD A hAH hA hAcard
    exact ((split_prime_orthogonal_plane_components_generate hnd hS3 hp hp3
      (by rw [hK]; exact hpq) A' hA' hAc').2 D' hD').2
  ·
    intro hn K _ _ hK b c hirr e D hD A hAH hA hAcard
    obtain ⟨-, hnd, hS3, -⟩ := coordinate_model_witness_minus h K hK b c hirr e
    refine matrix_model_of_intrinsic (d := 2 * n) (by omega) (coordinateQuadMinus n K hn b c) hnd
      hS3 (fun D' hD' A' hA' hAc' => ?_) D hD A hAH hA hAcard
    exact ((split_prime_orthogonal_plane_components_generate hnd hS3 hp hp3
      (by rw [hK]; exact hpq) A' hA' hAc').2 D' hD').2

end CFSG.RankThree.PartOne
