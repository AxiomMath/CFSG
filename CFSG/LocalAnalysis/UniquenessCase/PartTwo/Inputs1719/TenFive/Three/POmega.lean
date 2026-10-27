module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.OmCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation

theorem involAt_POmegaOdd : InvolAt .POmegaOdd := by
  intro S _ _ n _ _ hS
  have hC := hS.statedClassicalModel (by decide)
  obtain ⟨⟨-, -, hn3, -⟩, K, hKf, hKfin, hKcard, ⟨φ⟩⟩ := hS.statedClassicalModel (by decide)
  let : Field K := hKf
  obtain ⟨-, hQ, hT, -⟩ := coordinate_model_witness_odd hC K hKcard φ
  have hrep := odd_orthogonal_involution_semilinear_representation .POmegaOdd (Or.inl rfl) hC
    K hKcard φ
  exact InvolGood.of_mulEquiv (coordinateOddWitnessEquiv K φ).symm
    (involGood_matrixProjectiveDerived_three (hKcard.trans (pow_one 3)) (by omega) hQ hT hrep)

theorem involAt_POmegaPlus : InvolAt .POmegaPlus := by
  intro S _ _ n _ _ hS
  have hC := hS.statedClassicalModel (by decide)
  obtain ⟨⟨-, -, hn4⟩, K, hKf, hKfin, hKcard, ⟨φ⟩⟩ := hS.statedClassicalModel (by decide)
  let : Field K := hKf
  obtain ⟨-, hQ, hT, -⟩ := coordinate_model_witness_plus hC K hKcard φ
  have hrep := odd_orthogonal_involution_semilinear_representation .POmegaPlus
    (Or.inr (Or.inl rfl)) hC K hKcard φ
  exact InvolGood.of_mulEquiv (coordinatePlusWitnessEquiv K φ).symm
    (involGood_matrixProjectiveDerived_three (hKcard.trans (pow_one 3)) (by omega) hQ hT hrep)

theorem involAt_POmegaMinus : InvolAt .POmegaMinus := by
  intro S _ _ n _ _ hS
  have hC := hS.statedClassicalModel (by decide)
  obtain ⟨⟨-, -, hn4⟩, K, hKf, hKfin, hKcard, b, c, hirr, ⟨φ⟩⟩ :=
    hS.statedClassicalModel (by decide)
  let : Field K := hKf
  obtain ⟨-, hQ, hT, -⟩ := coordinate_model_witness_minus hC K hKcard b c hirr φ
  have hrep := odd_orthogonal_involution_semilinear_representation .POmegaMinus
    (Or.inr (Or.inr rfl)) hC (by omega) K hKcard b c hirr φ
  exact InvolGood.of_mulEquiv (coordinateMinusWitnessEquiv K (by omega) b c φ).symm
    (involGood_matrixProjectiveDerived_three (hKcard.trans (pow_one 3)) (by omega) hQ hT hrep)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
