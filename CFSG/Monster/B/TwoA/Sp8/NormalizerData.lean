
module


public import CFSG.Monster.B.TwoA.Sp8.A8

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA

@[expose] def Lgrp :
    Subgroup Dfull := Subgroup.centralizer (A8 : Set Dfull)

@[expose] def bA
    (x y : A8) : ZMod 2 :=
  b0 (Multiplicative.toAdd (aEquiv.symm x)) (Multiplicative.toAdd (aEquiv.symm y))

theorem bA_aEquiv
    (v w : Fin 8 → ZMod 2) :
    bA (aEquiv (Multiplicative.ofAdd v)) (aEquiv (Multiplicative.ofAdd w)) = b0 v w := by
  rw [bA, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply, toAdd_ofAdd, toAdd_ofAdd]

end CFSG.Monster.B.TwoA.Sp8
