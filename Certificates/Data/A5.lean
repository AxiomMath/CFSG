module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG

noncomputable section

open scoped MatrixGroups
open scoped Matrix
open Equiv.Perm

namespace GorensteinWalter

universe u

@[expose] abbrev A5SL2 := Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)

instance : DecidableEq (Equiv.Perm (Fin 5)) := fun a b =>
  decidable_of_iff (∀ i : Fin 5, a i = b i) ⟨Equiv.ext, fun h i => congrArg (fun e => e i) h⟩

instance : DecidablePred (fun σ : Equiv.Perm (Fin 5) => σ ∈ alternatingGroup (Fin 5)) :=
  sign.decidableMemKer

@[expose] def repMat0 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![1, 0; 0, 1], by decide⟩
@[expose] def sigma1 : Equiv.Perm (Fin 5) := Equiv.swap (0 : Fin 5) (1 : Fin 5) * Equiv.swap (2 : Fin 5) (3 : Fin 5)
@[expose] def repMat1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![0, 1; 4, 0], by decide⟩
@[expose] def sigma2 : Equiv.Perm (Fin 5) := Equiv.swap (0 : Fin 5) (2 : Fin 5) * Equiv.swap (2 : Fin 5) (4 : Fin 5)
@[expose] def repMat2 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![0, 1; 4, 4], by decide⟩
@[expose] def repMat3 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![4, 0; 1, 4], by decide⟩
@[expose] def repMat4 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![4, 4; 0, 4], by decide⟩
@[expose] def repMat5 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![4, 4; 1, 0], by decide⟩
@[expose] def repMat6 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![1, 4; 1, 0], by decide⟩
@[expose] def repMat7 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![1, 4; 0, 1], by decide⟩
@[expose] def repMat8 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![0, 4; 1, 2], by decide⟩
@[expose] def repMat9 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![1, 0; 1, 1], by decide⟩
@[expose] def repMat10 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![1, 0; 3, 1], by decide⟩
@[expose] def repMat11 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![0, 1; 4, 1], by decide⟩
@[expose] def repMat12 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![1, 2; 0, 1], by decide⟩
@[expose] def repMat13 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![1, 2; 4, 4], by decide⟩
@[expose] def repMat14 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![1, 1; 3, 4], by decide⟩
@[expose] def repMat15 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![3, 1; 4, 0], by decide⟩
@[expose] def repMat16 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![3, 1; 1, 4], by decide⟩
@[expose] def repMat17 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![4, 1; 1, 3], by decide⟩
@[expose] def repMat18 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![0, 1; 4, 2], by decide⟩
@[expose] def repMat19 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![4, 4; 4, 3], by decide⟩
@[expose] def repMat20 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![3, 4; 4, 4], by decide⟩
@[expose] def repMat21 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![3, 4; 1, 0], by decide⟩
@[expose] def repMat22 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![4, 0; 3, 4], by decide⟩
@[expose] def repMat23 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![1, 4; 2, 4], by decide⟩
@[expose] def repMat24 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![1, 3; 1, 4], by decide⟩
@[expose] def repMat25 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![1, 3; 0, 1], by decide⟩
@[expose] def repMat26 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![4, 2; 1, 2], by decide⟩
@[expose] def repMat27 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![4, 3; 2, 3], by decide⟩
@[expose] def repMat28 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![4, 4; 3, 2], by decide⟩
@[expose] def repMat29 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![3, 4; 3, 1], by decide⟩
@[expose] def repMat30 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![2, 4; 2, 2], by decide⟩
@[expose] def repMat31 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![1, 4; 3, 3], by decide⟩
@[expose] def repMat32 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![1, 2; 1, 3], by decide⟩
@[expose] def repMat33 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![2, 3; 1, 2], by decide⟩
@[expose] def repMat34 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![2, 3; 4, 4], by decide⟩
@[expose] def repMat35 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![3, 2; 3, 4], by decide⟩
@[expose] def repMat36 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![3, 1; 2, 1], by decide⟩
@[expose] def repMat37 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![2, 2; 3, 1], by decide⟩
@[expose] def repMat38 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![2, 2; 1, 4], by decide⟩
@[expose] def repMat39 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![3, 3; 1, 3], by decide⟩
@[expose] def repMat40 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![1, 3; 3, 0], by decide⟩
@[expose] def repMat41 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![1, 2; 2, 0], by decide⟩
@[expose] def repMat42 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![3, 4; 2, 3], by decide⟩
@[expose] def repMat43 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![2, 1; 0, 3], by decide⟩
@[expose] def repMat44 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![3, 1; 0, 2], by decide⟩
@[expose] def repMat45 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![1, 3; 2, 2], by decide⟩
@[expose] def repMat46 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![3, 0; 4, 2], by decide⟩
@[expose] def repMat47 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![3, 0; 1, 2], by decide⟩
@[expose] def repMat48 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![2, 0; 2, 3], by decide⟩
@[expose] def repMat49 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![2, 3; 0, 3], by decide⟩
@[expose] def repMat50 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![0, 3; 3, 4], by decide⟩
@[expose] def repMat51 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![0, 3; 3, 1], by decide⟩
@[expose] def repMat52 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![0, 2; 2, 2], by decide⟩
@[expose] def repMat53 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![2, 2; 2, 0], by decide⟩
@[expose] def repMat54 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![2, 3; 3, 0], by decide⟩
@[expose] def repMat55 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![0, 3; 3, 2], by decide⟩
@[expose] def repMat56 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![2, 2; 0, 3], by decide⟩
@[expose] def repMat57 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![2, 0; 3, 3], by decide⟩
@[expose] def repMat58 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![3, 0; 0, 2], by decide⟩
@[expose] def repMat59 : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ⟨!![0, 3; 3, 0], by decide⟩

@[expose] def repPerm : Equiv.Perm (Fin 5) → A5SL2 := fun σ =>
  match (σ 0).val, (σ 1).val, (σ 2).val, (σ 3).val with
  | 0, 1, 2, 3 => repMat0
  | 1, 0, 3, 2 => repMat1
  | 2, 1, 4, 3 => repMat2
  | 1, 2, 3, 4 => repMat3
  | 3, 0, 4, 2 => repMat4
  | 4, 1, 0, 3 => repMat5
  | 0, 3, 2, 4 => repMat6
  | 1, 4, 3, 0 => repMat7
  | 3, 2, 0, 4 => repMat8
  | 4, 0, 1, 2 => repMat9
  | 2, 3, 4, 0 => repMat10
  | 0, 4, 2, 1 => repMat11
  | 2, 3, 1, 4 => repMat12
  | 3, 4, 2, 0 => repMat13
  | 0, 2, 1, 4 => repMat14
  | 3, 2, 4, 1 => repMat15
  | 4, 3, 0, 2 => repMat16
  | 2, 0, 4, 1 => repMat17
  | 4, 3, 1, 0 => repMat18
  | 2, 4, 3, 1 => repMat19
  | 1, 3, 0, 4 => repMat20
  | 2, 4, 1, 0 => repMat21
  | 3, 4, 0, 1 => repMat22
  | 4, 2, 1, 3 => repMat23
  | 3, 1, 4, 0 => repMat24
  | 4, 2, 0, 1 => repMat25
  | 0, 3, 1, 2 => repMat26
  | 4, 0, 3, 1 => repMat27
  | 1, 3, 2, 0 => repMat28
  | 3, 0, 2, 1 => repMat29
  | 0, 4, 1, 3 => repMat30
  | 3, 1, 0, 2 => repMat31
  | 1, 2, 0, 3 => repMat32
  | 4, 1, 2, 0 => repMat33
  | 0, 2, 3, 1 => repMat34
  | 1, 3, 4, 2 => repMat35
  | 2, 1, 3, 0 => repMat36
  | 1, 4, 0, 2 => repMat37
  | 2, 0, 1, 3 => repMat38
  | 3, 1, 2, 4 => repMat39
  | 1, 4, 2, 3 => repMat40
  | 0, 1, 4, 2 => repMat41
  | 0, 2, 4, 3 => repMat42
  | 4, 1, 3, 2 => repMat43
  | 1, 0, 2, 4 => repMat44
  | 2, 0, 3, 4 => repMat45
  | 0, 4, 3, 2 => repMat46
  | 1, 0, 4, 3 => repMat47
  | 2, 1, 0, 4 => repMat48
  | 2, 4, 0, 3 => repMat49
  | 4, 0, 2, 3 => repMat50
  | 0, 1, 3, 4 => repMat51
  | 1, 2, 4, 0 => repMat52
  | 4, 2, 3, 0 => repMat53
  | 3, 0, 1, 4 => repMat54
  | 3, 4, 1, 2 => repMat55
  | 0, 3, 4, 1 => repMat56
  | 4, 3, 2, 1 => repMat57
  | 3, 2, 1, 0 => repMat58
  | 2, 3, 0, 1 => repMat59
  | _, _, _, _ => 1

@[expose] def a5x : alternatingGroup (Fin 5) := ⟨sigma1, by decide⟩
@[expose] def a5y : alternatingGroup (Fin 5) := ⟨sigma2, by decide⟩

@[expose] def a5E : A5SL2 := ⟨!![1, 1; 0, 1], by decide⟩
@[expose] def a5F : A5SL2 := ⟨!![1, 0; 1, 1], by decide⟩

@[expose] abbrev CenterEq (M : A5SL2) : Prop := M = 1 ∨ M = -1

end GorensteinWalter

end

end CFSG
