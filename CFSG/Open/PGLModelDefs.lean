module

public import Mathlib
public import CFSG.Open.MatrixModelCore

public section

namespace CFSG.PGLModel

open Matrix

@[expose] noncomputable def projImage {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K]
    (H : Subgroup (GL ι K)) : Subgroup (ProjGenLinGroup ι K) :=
  H.map ProjGenLinGroup.mk

@[expose] noncomputable def projSL (n : ℕ) (K : Type*) [Field K] :
    Subgroup (ProjGenLinGroup (Fin n) K) :=
  projImage (matrix_model% CFSG.MatrixModel.slCore (Fin n) K)

@[expose] noncomputable def projSU (n p f : ℕ) [Fact p.Prime] :
    Subgroup (ProjGenLinGroup (Fin n) (GaloisField p (2 * f))) :=
  projImage (Subgroup.closure {A : GL (Fin n) (GaloisField p (2 * f)) |
    GeneralLinearGroup.det A = 1 ∧
    ((A : Matrix (Fin n) (Fin n) (GaloisField p (2 * f))).map (· ^ (p ^ f)))ᵀ *
      (A : Matrix (Fin n) (Fin n) (GaloisField p (2 * f))) = 1})

@[expose] def sympForm (n : ℕ) (K : Type*) [Field K] : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K :=
  Matrix.fromBlocks 0 1 (-1) 0

@[expose] noncomputable def projSp (n : ℕ) (K : Type*) [Field K] :
    Subgroup (ProjGenLinGroup (Fin n ⊕ Fin n) K) :=
  projImage (matrix_model% CFSG.MatrixModel.gramCore (sympForm n K))

@[expose] def orthogonalGroup {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (Q : (ι → K) → K) :
    Subgroup (GL ι K) :=
  matrix_model% CFSG.MatrixModel.isometryCore Q

@[expose] def omegaModel {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K] (Q : (ι → K) → K) :
    Subgroup (Matrix.ProjGenLinGroup ι K) :=
  ⁅orthogonalGroup Q, orthogonalGroup Q⁆.map Matrix.ProjGenLinGroup.mk

@[expose] def minusQuadForm (m : ℕ) {K : Type*} [Field K] (b c : K)
    (v : Fin m ⊕ Fin m ⊕ Fin 2 → K) : K :=
  matrix_model% CFSG.MatrixModel.minusQuadCore m K b c v

@[expose] noncomputable def orthogonalMinus (m : ℕ) (K : Type*) [Field K] (b c : K) :
    Subgroup (GL (Fin m ⊕ Fin m ⊕ Fin 2) K) :=
  orthogonalGroup (minusQuadForm m b c)

@[expose] noncomputable def projOmegaMinus (m : ℕ) (K : Type*) [Field K] (b c : K) :
    Subgroup (ProjGenLinGroup (Fin m ⊕ Fin m ⊕ Fin 2) K) :=
  projImage ⁅orthogonalMinus m K b c, orthogonalMinus m K b c⁆

@[expose] def plusQuadForm (m : ℕ) {K : Type*} [Field K] (v : Fin m ⊕ Fin m → K) : K :=
  matrix_model% CFSG.MatrixModel.plusQuadCore m K v

@[expose] noncomputable def orthogonalPlus (m : ℕ) (K : Type*) [Field K] :
    Subgroup (GL (Fin m ⊕ Fin m) K) :=
  orthogonalGroup (plusQuadForm m (K := K))

@[expose] noncomputable def projOmegaPlus (m : ℕ) (K : Type*) [Field K] :
    Subgroup (ProjGenLinGroup (Fin m ⊕ Fin m) K) :=
  projImage ⁅orthogonalPlus m K, orthogonalPlus m K⁆

@[expose] def IModel (G : Type*) [Group G] : Prop :=
  ∃ f : ℕ, 1 ≤ f ∧
    (Nonempty (G ≃* projSU 5 2 f) ∨
      (∃ b c : GaloisField 2 f, (∀ s : GaloisField 2 f, s ^ 2 + b * s + c ≠ 0) ∧
        Nonempty (G ≃* projOmegaMinus 3 (GaloisField 2 f) b c)) ∨
      Nonempty (G ≃* projSL 4 (GaloisField 2 f)) ∨
      Nonempty (G ≃* projSp 3 (GaloisField 2 f)))

end CFSG.PGLModel
