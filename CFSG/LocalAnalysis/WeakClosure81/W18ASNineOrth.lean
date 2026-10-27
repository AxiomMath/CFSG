module

public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineOrthBridge
import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.SeitzReduction.F4Pilot (one_le_of_natCard_eq_two_pow)

theorem noSocle185Factor_statedOmega_quadPlus (hO : LieOrderFormulasInput) {F : Type} [Field F]
    [Finite F] {k n : ℕ} (hF : Nat.card F = 2 ^ n) (hk : 4 ≤ k) :
    NoSocle185Factor ↥(StatedOmega (StatedQuadPlus k F)) := by
  have hadm : StatedLieAdmissible .POmegaPlus k 2 n :=
    ⟨Nat.prime_two, one_le_of_natCard_eq_two_pow hF, hk⟩
  haveI : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadPlus k F))) :=
    CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadPlus (by omega)
  refine NoSocle185Factor.of_statedProj _ (NoSocle185Factor.of_lieModel_two hO hadm ?_ ?_)
  · exact Or.inl ⟨by decide, hadm, F, inferInstance, inferInstance, hF, ⟨MulEquiv.refl _⟩⟩
  · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> exact absurd h (by decide)

theorem noSocle185Factor_statedOmega_quadMinus (hO : LieOrderFormulasInput) {F : Type} [Field F]
    [Finite F] {k n : ℕ} (hF : Nat.card F = 2 ^ n) (hk : 4 ≤ k) {b c : F}
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    NoSocle185Factor ↥(StatedOmega (StatedQuadMinus k F b c)) := by
  have hadm : StatedLieAdmissible .POmegaMinus k 2 n :=
    ⟨Nat.prime_two, one_le_of_natCard_eq_two_pow hF, hk⟩
  haveI : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadMinus k F b c))) :=
    CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadMinus hk hbc
  refine NoSocle185Factor.of_statedProj _ (NoSocle185Factor.of_lieModel_two hO hadm ?_ ?_)
  · exact Or.inl ⟨by decide, hadm, F, inferInstance, inferInstance, hF, b, c, hbc,
      ⟨MulEquiv.refl _⟩⟩
  · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> exact absurd h (by decide)

theorem noSocle185Factor_orthogonalPlus (hO : LieOrderFormulasInput) {F : Type} [Field F]
    [Finite F] {k n : ℕ} (hF : Nat.card F = 2 ^ n) (hk : 4 ≤ k) :
    NoSocle185Factor ↥(CFSG.PGLModel.orthogonalPlus k F) :=
  noSocle185Factor_orthogonalPlus_of_statedOmega k (noSocle185Factor_statedOmega_quadPlus hO hF hk)

theorem noSocle185Factor_orthogonalMinus (hO : LieOrderFormulasInput) {F : Type} [Field F]
    [Finite F] {k n : ℕ} (hF : Nat.card F = 2 ^ n) (hk : 3 ≤ k) {b c : F}
    (hbc : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    NoSocle185Factor ↥(CFSG.PGLModel.orthogonalMinus k F b c) :=
  noSocle185Factor_orthogonalMinus_of_statedOmega k b c
    (noSocle185Factor_statedOmega_quadMinus hO hF (by omega) hbc)

end CFSG.LocalAnalysis.WeakClosure81

end
