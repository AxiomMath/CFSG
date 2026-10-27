module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelImage
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbitModel
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelFamily

public section

namespace CFSG.RankThree.PartOne.KCOrthogonalAut

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  (orthogonal_geometry_tail_model_point_family_invariant)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  (coordinate_plus_pointFamilyAut_eq_top)

section Tags

variable (K : Type) [Field K] [Finite K]

theorem exists_card_eq_pow : ∃ f : ℕ, 1 ≤ f ∧ Nat.card K = ringChar K ^ f := by
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K (ringChar K)
  exact ⟨n, n.pos, by rw [Nat.card_eq_fintype_card, hn]⟩

theorem matrixProjectiveImage_eq_top_odd (n : ℕ) (hn : 3 ≤ n) (h2 : ringChar K ≠ 2) :
    matrixProjectiveImage (coordinateQuadOdd n K) = ⊤ := by
  obtain ⟨f, hf, hK⟩ := exists_card_eq_pow K
  have hp : (ringChar K).Prime := CharP.char_is_prime K _
  have hmod : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadOdd n K))) .POmegaOdd n
      (ringChar K) f := ⟨⟨hp, hf, hn, h2⟩, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  have h1 := (orthogonal_geometry_tail_model_point_family_invariant _ .POmegaOdd (Or.inl rfl) n
    (ringChar K) f hmod K hK).2
  have h2' := coordinate_odd_family_eq_matrixImage hmod K hK (MulEquiv.refl _)
  rw [← h2', h1]

theorem matrixProjectiveImage_eq_top_plus (n : ℕ) (hn : 5 ≤ n) :
    matrixProjectiveImage (coordinateQuadPlus n K) = ⊤ := by
  obtain ⟨f, hf, hK⟩ := exists_card_eq_pow K
  have hp : (ringChar K).Prime := CharP.char_is_prime K _
  have hmod : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus n K))) .POmegaPlus n
      (ringChar K) f := ⟨⟨hp, hf, by omega⟩, K, inferInstance, inferInstance, hK,
    ⟨MulEquiv.refl _⟩⟩
  have h1 := coordinate_plus_pointFamilyAut_eq_top (K := K) hn
  have h2' := coordinate_plus_family_eq_matrixImage hmod K hK (MulEquiv.refl _)
  rw [← h2', h1]

theorem matrixProjectiveImage_eq_top_minus (n : ℕ) (hn : 4 ≤ n) (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    matrixProjectiveImage (coordinateQuadMinus n K (by omega) b c) = ⊤ := by
  obtain ⟨f, hf, hK⟩ := exists_card_eq_pow K
  have hp : (ringChar K).Prime := CharP.char_is_prime K _
  have hmod : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadMinus n K b c)))
      .POmegaMinus n (ringChar K) f := ⟨⟨hp, hf, hn⟩, K, inferInstance, inferInstance, hK, b, c,
    hirr, ⟨MulEquiv.refl _⟩⟩
  have h1 := (orthogonal_geometry_tail_model_point_family_invariant _ .POmegaMinus (Or.inr rfl) n
    (ringChar K) f hmod (by omega) K hK b c hirr).2
  have h2' := coordinate_minus_family_eq_matrixImage hmod (by omega) K hK b c hirr
    (MulEquiv.refl _)
  rw [← h2', h1]

end Tags

end CFSG.RankThree.PartOne.KCOrthogonalAut
