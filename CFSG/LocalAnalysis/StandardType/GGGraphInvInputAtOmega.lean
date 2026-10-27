module

public import CFSG.LocalAnalysis.StandardType.GGGraphInvInputModelTransport
public import CFSG.LocalAnalysis.StandardType.GGGraphInvInputModelMinus
public import CFSG.LocalAnalysis.StandardType.GGGraphInvInputModelPlusFour

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.RankThree.PartOne.AUTSL

private theorem ggOmW6e_modelAt_POmegaMinus
    (n f : ℕ)
    (hadm : StatedLieAdmissible .POmegaMinus n 2 f) :
    ∃ (C : Type) (_ : Group C) (π : (ggU .POmegaMinus n f).K →* C),
      Function.Surjective π ∧ π.ker = Subgroup.center (ggU .POmegaMinus n f).K ∧
      GGGraphInvInputModel C := by
  obtain ⟨-, _, hn4⟩ := hadm
  have hirr := minusCoeffs_irr 2 f
  exact ⟨matrixDerived (Qm n hn4 (minusCoeffs 2 f).1 (minusCoeffs 2 f).2), inferInstance,
    AutOm.spinModelMinus hn4 hirr, AutOm.spinModelMinus_surjective hn4 hirr,
    AutOm.ker_spinModelMinus hn4 hirr, ggGraphInvInputModel_minus hn4 hirr⟩

theorem ggGraphInvInputModelAt_POmegaMinus
    : GGGraphInvInputModelAt .POmegaMinus := by
  intro n f hadm hrank
  exact ggOmW6e_modelAt_POmegaMinus n f hadm

private theorem ggOmW6e_modelAt_POmegaPlus_of_five
    (n f : ℕ) (hn5 : 5 ≤ n) :
    ∃ (C : Type) (_ : Group C) (π : (ggU .POmegaPlus n f).K →* C),
      Function.Surjective π ∧ π.ker = Subgroup.center (ggU .POmegaPlus n f).K ∧
      GGGraphInvInputModel C := by
  have hn : 3 ≤ n := by omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [show ggU .POmegaPlus n f = ⟨spinGroup (CFSG.LieType.Universal.Spin.quadPlus n
        (GaloisField 2 f)),
      CFSG.LieType.Universal.Spin.plusDatum n (GaloisField 2 f) hn⟩ from dite_eq_left hn]
  exact ⟨matrixDerived (coordinateQuadPlus n (GaloisField 2 f)), inferInstance,
    AutOm.spinModelPlus hn, AutOm.spinModelPlus_surjective hn, AutOm.ker_spinModelPlus hn,
    ggGraphInvInputModel_plus hn5⟩

private theorem ggOmW6e_modelAt_POmegaPlus_of_four
    (f : ℕ) :
    ∃ (C : Type) (_ : Group C) (π : (ggU .POmegaPlus 4 f).K →* C),
      Function.Surjective π ∧ π.ker = Subgroup.center (ggU .POmegaPlus 4 f).K ∧
      GGGraphInvInputModel C := by
  have h4 : 3 ≤ 4 := by norm_num
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [ggU_POmegaPlus_eq h4]
  exact ⟨Triality.Om8 (GaloisField 2 f), inferInstance,
    AutOm.spinModelPlus h4, AutOm.spinModelPlus_surjective h4, AutOm.ker_spinModelPlus h4,
    ggGraphInvInputModel_plus_four⟩

theorem ggGraphInvInputModelAt_POmegaPlus
    : GGGraphInvInputModelAt .POmegaPlus := by
  intro n f hadm hrank
  have hn4 : 4 ≤ n := by
    obtain ⟨-, -, hn4⟩ := hadm
    exact hn4
  rcases (show n = 4 ∨ 5 ≤ n by omega) with rfl | hn5
  · exact ggOmW6e_modelAt_POmegaPlus_of_four f
  · exact ggOmW6e_modelAt_POmegaPlus_of_five n f hn5

theorem ggGraphInvInputAt_POmegaPlus
    : GGGraphInvInputAt .POmegaPlus :=
  ggGraphInvInputAt_of_model (Or.inr (Or.inl rfl)) ggGraphInvInputModelAt_POmegaPlus

theorem ggGraphInvInputAt_POmegaMinus
    : GGGraphInvInputAt .POmegaMinus :=
  ggGraphInvInputAt_of_model (Or.inr (Or.inr (Or.inl rfl))) ggGraphInvInputModelAt_POmegaMinus

end CFSG.StandardType
