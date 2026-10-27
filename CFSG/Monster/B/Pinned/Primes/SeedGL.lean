module

public import CFSG.Monster.B.Final.Basic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Monster.B.Pinned.Primes.Program

public section

namespace CFSG.Monster.B.Pinned

open CFSG.Blueprint

theorem finite_B : Finite NativeSporadic.B := Finite.of_injective _ bMat_injective

theorem genA₁_det_ne_zero : genA₁.det ≠ 0 := by
  rw [B_generator_determinants.1]
  exact one_ne_zero

theorem genA₂_det_ne_zero : genA₂.det ≠ 0 := by
  rw [B_generator_determinants.2.1]
  exact one_ne_zero

noncomputable abbrev glA₁ : GL (Fin 4370) (ZMod 2) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero genA₁ genA₁_det_ne_zero

noncomputable abbrev glA₂ : GL (Fin 4370) (ZMod 2) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero genA₂ genA₂_det_ne_zero

@[expose] noncomputable def bSeedGL :
    NativeSporadic.B ≃* Subgroup.closure ({glA₁, glA₂} : Set (GL (Fin 4370) (ZMod 2))) :=
  NativeSporadic.matrixSeedEquiv 2 4370 (by norm_num) genA₁ genA₂ genA₁_det_ne_zero
    genA₂_det_ne_zero

theorem coe_bSeedGL (u : NativeSporadic.B) :
    (((bSeedGL u : GL (Fin 4370) (ZMod 2))) : Matrix (Fin 4370) (Fin 4370) (ZMod 2)) = bMat u :=
  rfl

@[expose] noncomputable def bGL : NativeSporadic.B →* GL (Fin 4370) (ZMod 2) :=
  Units.map (NativeSporadic.seedMonoid 2 4370 1 NativeSporadic.BSeed1 NativeSporadic.BSeed2).subtype

theorem coe_bGL (u : NativeSporadic.B) :
    ((bGL u : GL (Fin 4370) (ZMod 2)) : Matrix (Fin 4370) (Fin 4370) (ZMod 2)) = bMat u := rfl

theorem bSeedGL_eq
    (u : NativeSporadic.B) : (bSeedGL u : GL (Fin 4370) (ZMod 2)) = bGL u :=
  Units.ext rfl

theorem bGL_bA₁ : bGL bA₁ = glA₁ := by
  apply Units.ext
  rw [coe_bGL, bMat_bA₁, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]

theorem bGL_bA₂ : bGL bA₂ = glA₂ := by
  apply Units.ext
  rw [coe_bGL, bMat_bA₂, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]

theorem bSeedGL_bA₁ :
    (bSeedGL bA₁ : GL (Fin 4370) (ZMod 2)) = glA₁ := by
  rw [bSeedGL_eq, bGL_bA₁]

theorem bSeedGL_bA₂ :
    (bSeedGL bA₂ : GL (Fin 4370) (ZMod 2)) = glA₂ := by
  rw [bSeedGL_eq, bGL_bA₂]

theorem bSeedGL_runG (prog : List Primes.Native.Ins) (k : ℕ) :
    (bSeedGL (runG prog bA₁ bA₂ k) : GL (Fin 4370) (ZMod 2)) = runG prog glA₁ glA₂ k := by
  rw [bSeedGL_eq, map_runG, bGL_bA₁, bGL_bA₂]

end CFSG.Monster.B.Pinned
