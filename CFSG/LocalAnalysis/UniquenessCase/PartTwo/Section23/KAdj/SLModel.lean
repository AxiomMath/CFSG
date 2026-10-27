module

public import CFSG.ClassicalInvolution.WeakCT.Blocks
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalInvolution.WeakCT CFSG.LocalAnalysis.UniquenessCase.UC22.KTabD
open CFSG.Open

abbrev slMat {k : ℕ} {K : Type} [Field K] (g : ↥(StatedSL k K)) : Matrix (Fin k) (Fin k) K :=
  ((g : GL (Fin k) K) : Matrix (Fin k) (Fin k) K)

@[expose] def slTorusDiag (k : ℕ) {K : Type} [Field K] (c : K) : Fin k → K :=
  fun i => if (i : ℕ) = 0 then c else if (i : ℕ) = 1 then c⁻¹ else 1

@[expose] def slAlphaCuts (k : ℕ) : Set ℕ := {i | 2 ≤ i ∧ i < k}

@[expose] noncomputable def slU (k : ℕ) (K : Type) [Field K] : Subgroup ↥(StatedSL k K) :=
  (LinearFlag.unitriangular k K).map (specialLinearGroupEquivStatedSL k K).toMonoidHom

@[expose] noncomputable def slQAlpha (k : ℕ) (K : Type) [Field K] : Subgroup ↥(StatedSL k K) :=
  (LinearFlag.flagStabilizer k K (slAlphaCuts k)).map
    (specialLinearGroupEquivStatedSL k K).toMonoidHom

abbrev slQZero (k : ℕ) [NeZero k] (K : Type) [Field K] : Subgroup ↥(StatedSL k K) :=
  lineStab (StatedSL k K) (Pi.single 0 1)

@[expose] noncomputable def slRootEmb (k : ℕ) (hk : 3 ≤ k) (K : Type) [Field K] :
    Matrix.SpecialLinearGroup (Fin 2) K →* ↥(StatedSL k K) :=
  (specialLinearGroupEquivStatedSL k K).toMonoidHom.comp (blockSL K k 2 1 (by omega))

@[expose] noncomputable def slRoot (k : ℕ) (hk : 3 ≤ k) (K : Type) [Field K] :
    Subgroup ↥(StatedSL k K) :=
  (slRootEmb k hk K).range

theorem slRootEmb_injective {k : ℕ} (hk : 3 ≤ k) {K : Type} [Field K] :
    Function.Injective (slRootEmb k hk K) :=
  (specialLinearGroupEquivStatedSL k K).injective.comp (blockSL_injective _)

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
