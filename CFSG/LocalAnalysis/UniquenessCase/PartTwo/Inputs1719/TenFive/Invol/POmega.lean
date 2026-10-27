module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.OmCore
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.Families

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation

theorem involQAt_POmegaOdd : InvolQAt .POmegaOdd := by
  intro S _ _ n p e hp2 h3 _ hS
  have hC := hS.statedClassicalModel (by decide)
  obtain ⟨⟨hp, -, hn3, -⟩, K, hKf, hKfin, hKcard, ⟨φ⟩⟩ := hS.statedClassicalModel (by decide)
  let : Field K := hKf
  obtain ⟨hchar, hQ, hT, -⟩ := coordinate_model_witness_odd hC K hKcard φ
  have : CharP K p := ringChar.of_eq hchar
  have hrep := odd_orthogonal_involution_semilinear_representation .POmegaOdd (Or.inl rfl) hC
    K hKcard φ
  exact InvolInvertsGood.of_mulEquiv (coordinateOddWitnessEquiv K φ).symm
    (involInvertsGood_matrixProjectiveDerived hp hp2 hKcard h3 (by omega) hQ hT hrep)

theorem involQAt_POmegaPlus : InvolQAt .POmegaPlus := by
  intro S _ _ n p e hp2 h3 _ hS
  have hC := hS.statedClassicalModel (by decide)
  obtain ⟨⟨hp, -, hn4⟩, K, hKf, hKfin, hKcard, ⟨φ⟩⟩ := hS.statedClassicalModel (by decide)
  let : Field K := hKf
  obtain ⟨hchar, hQ, hT, -⟩ := coordinate_model_witness_plus hC K hKcard φ
  have : CharP K p := ringChar.of_eq hchar
  have hrep := odd_orthogonal_involution_semilinear_representation .POmegaPlus
    (Or.inr (Or.inl rfl)) hC K hKcard φ
  exact InvolInvertsGood.of_mulEquiv (coordinatePlusWitnessEquiv K φ).symm
    (involInvertsGood_matrixProjectiveDerived hp hp2 hKcard h3 (by omega) hQ hT hrep)

theorem involQAt_POmegaMinus : InvolQAt .POmegaMinus := by
  intro S _ _ n p e hp2 h3 _ hS
  have hC := hS.statedClassicalModel (by decide)
  obtain ⟨⟨hp, -, hn4⟩, K, hKf, hKfin, hKcard, b, c, hirr, ⟨φ⟩⟩ :=
    hS.statedClassicalModel (by decide)
  let : Field K := hKf
  obtain ⟨hchar, hQ, hT, -⟩ := coordinate_model_witness_minus hC K hKcard b c hirr φ
  have : CharP K p := ringChar.of_eq hchar
  have hrep := odd_orthogonal_involution_semilinear_representation .POmegaMinus
    (Or.inr (Or.inr rfl)) hC (by omega) K hKcard b c hirr φ
  exact InvolInvertsGood.of_mulEquiv (coordinateMinusWitnessEquiv K (by omega) b c φ).symm
    (involInvertsGood_matrixProjectiveDerived hp hp2 hKcard h3 (by omega) hQ hT hrep)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
