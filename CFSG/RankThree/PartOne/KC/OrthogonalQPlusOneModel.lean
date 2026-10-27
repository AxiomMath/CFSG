module

public import CFSG.RankThree.PartOne.KC.OrthogonalQPlusOneD4
public import CFSG.RankThree.PartOne.KC.OrthogonalMatrixModelTransport

public section

open CFSG CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.RankThree.PartOne.KCOrthogonalAut CFSG.RankThree.PartOne.KCOrthogonalModel

namespace CFSG.RankThree.PartOne

@[expose] def CommonLayerCentralizerTrivial (P : Type) [Group P] (p : ℕ) : Prop :=
  ∀ D : Subgroup (MulAut P), OuterAutomorphisms.inner P ≤ D →
    ∀ A : Subgroup (MulAut P), A ≤ OuterAutomorphisms.inner P → IsElementaryAbelian p A →
      Nat.card A = p ^ 2 →
        (⨅ (a : MulAut P) (_ : a ∈ A ∧ a ≠ 1),
          Subgroup.centralizer (((CFSG.layer ↥(D ⊓ Subgroup.centralizer
              ({a} : Set (MulAut P)))).map
            (D ⊓ Subgroup.centralizer ({a} : Set (MulAut P))).subtype : Subgroup (MulAut P)) :
            Set (MulAut P))) = ⊥

theorem orthogonal_inner_plane_common_centralizer_q_plus_one (G : Type) [Group G]
    (t : StatedLieTag) (ht : t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (n ℓ f p : ℕ) (h : StatedClassicalModel G t n ℓ f) :
    p.Prime → 3 < p → p ≠ ℓ → p ∣ ℓ ^ f + 1 →
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
          CommonLayerCentralizerTrivial (matrixProjectiveDerived (coordinateQuadMinus n K hn b c)) p
    | _ => False := by
  intro hp hp3 hpℓ hpq
  rcases ht with rfl | rfl | rfl
  ·
    intro K _ _ hK e D hD A hAH hA hAcard
    obtain ⟨-, -, hn3, hℓ2⟩ := h.1
    obtain ⟨hchar, hnd, hS3, -⟩ := coordinate_model_witness_odd h K hK e
    have hpl : p ≠ ringChar K := by
      rw [hchar]
      exact hpℓ
    have hpK : p ∣ Nat.card K + 1 := by
      rw [hK]
      exact hpq
    have h2 : ringChar K ≠ 2 := by
      rw [hchar]
      exact hℓ2
    refine matrix_model_of_intrinsic (d := 2 * n + 1) (by omega) (coordinateQuadOdd n K) hnd hS3
      (fun D' hD' A' hA' hAc' => ?_) D hD A hAH hA hAcard
    exact orthogonal_inner_plane_common_centralizer_q_plus_one_of_natural _ hnd hS3 hp hp3 hpl hpK
      D' hD' A' hA' hAc' fun α _ => inducedBySemilinear_of_image_eq_top (by omega) _
        (matrixProjectiveImage_eq_top_odd K n hn3 h2) α
  ·
    intro K _ _ hK e D hD A hAH hA hAcard
    obtain ⟨-, -, hn4⟩ := h.1
    obtain ⟨hchar, hnd, hS3, -⟩ := coordinate_model_witness_plus h K hK e
    have hpl : p ≠ ringChar K := by
      rw [hchar]
      exact hpℓ
    have hpK : p ∣ Nat.card K + 1 := by
      rw [hK]
      exact hpq
    refine matrix_model_of_intrinsic (d := 2 * n) (by omega) (coordinateQuadPlus n K) hnd hS3
      (fun D' hD' A' hA' hAc' => ?_) D hD A hAH hA hAcard
    by_cases hn : n = 4
    · subst hn
      exact orthogonal_inner_plane_common_centralizer_q_plus_one_d4 G h K hK e hp hp3 hpℓ hpK D' hD'
        A' hA' hAc'
    · have hn5 : 5 ≤ n := by omega
      exact orthogonal_inner_plane_common_centralizer_q_plus_one_of_natural _ hnd hS3 hp hp3 hpl
        hpK D' hD' A' hA' hAc' fun α _ => inducedBySemilinear_of_image_eq_top (by omega) _
          (matrixProjectiveImage_eq_top_plus K n hn5) α
  ·
    intro hn K _ _ hK b c hirr e D hD A hAH hA hAcard
    obtain ⟨-, -, hn4⟩ := h.1
    obtain ⟨hchar, hnd, hS3, -⟩ := coordinate_model_witness_minus h K hK b c hirr e
    have hpl : p ≠ ringChar K := by
      rw [hchar]
      exact hpℓ
    have hpK : p ∣ Nat.card K + 1 := by
      rw [hK]
      exact hpq
    refine matrix_model_of_intrinsic (d := 2 * n) (by omega) (coordinateQuadMinus n K hn b c) hnd
      hS3 (fun D' hD' A' hA' hAc' => ?_) D hD A hAH hA hAcard
    exact orthogonal_inner_plane_common_centralizer_q_plus_one_of_natural _ hnd hS3 hp hp3 hpl hpK
      D' hD' A' hA' hAc' fun α _ => inducedBySemilinear_of_image_eq_top (by omega) _
        (matrixProjectiveImage_eq_top_minus K n hn4 b c hirr) α

end CFSG.RankThree.PartOne
