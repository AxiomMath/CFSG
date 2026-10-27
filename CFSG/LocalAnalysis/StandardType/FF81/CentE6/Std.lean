module

public import CFSG.Holt.SL6.Defs
public import CFSG.RankThree.GF2n.Smith81.S81A5Basic
public import Mathlib

public section

namespace CFSG.StandardType.FF81.CentE6

open scoped MatrixGroups
open CFSG.RankThree.GF2n.Smith81

@[expose] noncomputable def elem (i j : Fin 6) : SL(6, ZMod 2) :=
  if h : i = j then 1 else Matrix.SpecialLinearGroup.transvection h 1

@[expose] noncomputable def Sone : Subgroup SL(6, ZMod 2) :=
  Subgroup.closure {g | ∃ j : Fin 6, 1 ≤ j.val ∧ g = elem 0 j}

@[expose] noncomputable def Ssix : Subgroup SL(6, ZMod 2) :=
  Subgroup.closure {g | ∃ i : Fin 6, i.val ≤ 4 ∧ g = elem i 5}

@[expose] noncomputable def Sgrp : Subgroup SL(6, ZMod 2) := Sone ⊔ Ssix

@[expose] noncomputable def Jgrp : Subgroup SL(6, ZMod 2) :=
  Subgroup.closure {g | ∃ i j : Fin 6, i ≠ j ∧ 1 ≤ i.val ∧ i.val ≤ 4 ∧ 1 ≤ j.val ∧ j.val ≤ 4 ∧
    g = elem i j}

@[expose] noncomputable def Dgrp : Subgroup SL(6, ZMod 2) :=
  Subgroup.closure {g | ∃ i j : Fin 6, i ≠ j ∧ 1 ≤ i.val ∧ i.val ≤ 3 ∧ 1 ≤ j.val ∧ j.val ≤ 3 ∧
    g = elem i j}

@[expose] noncomputable def bStd : SL(6, ZMod 2) := elem 1 2 * elem 2 1

@[expose] def IsTransvec (g : SL(6, ZMod 2)) : Prop :=
  Matrix.rank ((g : Matrix (Fin 6) (Fin 6) (ZMod 2)) - 1) = 1

@[expose] noncomputable def cubeAct (g : SL(6, ZMod 2)) :
    A5Cube.Cube (ZMod 2) →ₗ[ZMod 2] A5Cube.Cube (ZMod 2) :=
  A5Cube.rho (ZMod 2) (Matrix.SpecialLinearGroup.toGL g)

@[expose] noncomputable def fixedDim (f : A5Cube.Cube (ZMod 2) →ₗ[ZMod 2] A5Cube.Cube (ZMod 2)) :
    ℕ :=
  Module.finrank (ZMod 2) (LinearMap.ker (f - 1))

@[expose] noncomputable def Wsp : Submodule (ZMod 2) (A5Cube.Cube (ZMod 2)) :=
  LinearMap.range (cubeAct CFSG.Holt.SL6.stdTransvection - 1)

structure CubeSetting (X : Type) [Group X] where
  L : Subgroup X
  eL : ↥L ≃* SL(6, ZMod 2)
  ρ : X →* (A5Cube.Cube (ZMod 2) →ₗ[ZMod 2] A5Cube.Cube (ZMod 2))
  hρ : ∀ l : ↥L, ρ l = cubeAct (eL l)

@[expose] def CubeSetting.img {X : Type} [Group X] (S : CubeSetting X)
    (A : Subgroup SL(6, ZMod 2)) : Subgroup X :=
  A.map (S.L.subtype.comp S.eL.symm.toMonoidHom)

@[expose] def CubeSetting.z {X : Type} [Group X] (S : CubeSetting X) : X :=
  (S.eL.symm CFSG.Holt.SL6.stdTransvection : X)

@[expose] noncomputable def CubeSetting.b {X : Type} [Group X] (S : CubeSetting X) : X :=
  (S.eL.symm bStd : X)

end CFSG.StandardType.FF81.CentE6
