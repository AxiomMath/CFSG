module

public import CFSG.LinearAlgebra.FixedPointFreeOrderThreeField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearCoordinates
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3F4Facts1
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3F4Facts3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3F4Facts4
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3F4Facts5
public import CFSG.GroupTheory.SteinbergBKSemilinearFixedBasis
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3NormalFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3MatrixCoreA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3MatrixCoreB
public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LinearAlgebra CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear Subgroup
  CFSG.Open

theorem s16h_e3_z3_matrix_core
    (N K : Subgroup (coordinateSemilinearGroup 3 OmegaField))
    (hKN : K ≤ N) (hKnorm : (K.subgroupOf N).Normal)
    (hO2 : ∀ P : Subgroup (coordinateSemilinearGroup 3 OmegaField), P ≤ K →
      (P.subgroupOf K).Normal → IsPGroup 2 P → P = ⊥)
    (hZK : ∀ c : OmegaFieldˣ, (SemidirectProduct.inl
      (Matrix.GeneralLinearGroup.scalar (Fin 3) c) : coordinateSemilinearGroup 3 OmegaField) ∈ K)
    {t : coordinateSemilinearGroup 3 OmegaField} (htK : t ∈ K) (ht2 : t ^ 2 = 1)
    (htn : SemidirectProduct.rightHom t ≠ 1)
    {u : Matrix.GeneralLinearGroup (Fin 3) OmegaField}
    (huK : (SemidirectProduct.inl u : coordinateSemilinearGroup 3 OmegaField) ∈ K)
    (hu2 : u ^ 2 = 1) (hu1 : u ≠ 1)
    {Q : Subgroup (coordinateSemilinearGroup 3 OmegaField)} (hQN : Q ≤ N)
    (hQ : IsElemAbelian 3 Q) (hQ9 : 9 ≤ Nat.card ↥Q) :
    ∃ P : Subgroup (coordinateSemilinearGroup 3 OmegaField),
      P ≤ K ∧ IsElemAbelian 3 P ∧ 9 ≤ Nat.card ↥P := by
  by_contra h
  have hno : ∀ P : Subgroup (coordinateSemilinearGroup 3 OmegaField), P ≤ K →
      IsElemAbelian 3 P → Nat.card ↥P < 9 := by
    intro P hPK hP
    exact not_le.1 fun h9 => h ⟨P, hPK, hP, h9⟩
  obtain ⟨F, hFcard, hFnorm, hFleK⟩ :=
    s16h_e3_z3_transvection_normal_five N K hKN hKnorm hO2 hZK hno huK hu2 hu1
  exact s16h_e3_z3_scalar_contra N K hKN hKnorm hno htK ht2 htn hQN hQ hQ9
    F hFcard hFnorm hFleK

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
