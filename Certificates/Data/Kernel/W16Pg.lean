module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWDef
public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.Spor.Chain
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.KC.W16Pg

open CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.Fin76b.W16 CFSG.KC.Enum CFSG.KS

@[expose] def invG (mul : Nat → Nat → Nat) (a : Nat) : Nat :=
  ((List.range 128).find? fun b => mul a b == 0).getD 0

@[expose] def commG (mul : Nat → Nat → Nat) (a b : Nat) : Nat :=
  mul (mul a b) (mul (invG mul a) (invG mul b))

@[expose] def candSetG (mul : Nat → Nat → Nat) (k : Nat) : List Nat :=
  (List.range 128).filter fun c =>
    c != 0 && c != tC && mul c c == mul baseArr[k]! baseArr[k]! &&
      (List.range k).all fun j => commG mul c baseArr[j]! == commG mul baseArr[k]! baseArr[j]!

@[expose] def tableG (mul : Nat → Nat → Nat) : Bool :=
  (List.range 128).all (fun a => (List.range 128).all fun b => decide (mul a b < 128)) &&
  (List.range 128).all (fun a => mul 0 a == a && mul a 0 == a && mul a (invG mul a) == 0 &&
      mul (invG mul a) a == 0 && decide (invG mul a < 128) && (mul a a == 0 || mul a a == tC)) &&
  (List.range 128).all (fun c =>
      !((List.range 128).all fun d => mul c d == mul d c) || c == 0 || c == tC) &&
  (List.range 128).all (fun d => mul tC d == mul d tC) &&
  mul tC tC == 0 && tC != 0 && decide (tC < 128)

@[expose] def genG (mul : Nat → Nat → Nat) : Bool :=
  decide (baseArr.size = 6) && decide (genElems.size = 128) && decide (genPar.size = 128) &&
    decide (genGen.size = 128) && (genElems[0]! == 0) &&
    (List.range 128).all (fun j => decide (genElems[j]! < 128)) &&
    (List.range 128).all (fun c => (List.range 128).any fun j => genElems[j]! == c) &&
    (List.range 127).all (fun j' => let j := j' + 1;
      decide (genPar[j]! < j) && decide (genGen[j]! < 6) &&
        (mul genElems[genPar[j]!]! baseArr[genGen[j]!]! == genElems[j]!)) &&
    baseArr.all (fun b => decide (b < 128))

@[expose] def candG (mul : Nat → Nat → Nat) : Bool :=
  ((List.range 6).map fun k => (candSetG mul k).length).prod == 3317760

@[expose] noncomputable def mulEK (ET : Nat → Nat) (a b : Nat) : Nat := pg 5 (mask 5) (ET a) b

@[expose] noncomputable def redPK (ET : Nat → Nat) (i k : Nat) : Nat × Nat :=
  if i = 0 ∨ i = 1 ∨ i = 4 ∨ i = 5 then (i, k) else (dMul i 2, mulEK ET k eT)

@[expose] noncomputable def ixPK (ET : Nat → Nat) (i k : Nat) : Nat :=
  32 * posD (redPK ET i k).1 + (redPK ET i k).2

@[expose] noncomputable def mulCK (ET : Nat → Nat) (a b : Nat) : Nat :=
  ixPK ET (dMul (decD a) (decD b)) (mulEK ET (a % 32) (b % 32))

@[expose] noncomputable def autK (ET S : Nat → Nat) : Bool :=
  (List.range 36).all fun j =>
    (List.range 128).all (fun a => decide (pg 8 (mask 8) (S j) a < 128)) &&
    (List.range 128).all (fun a => (List.range 128).all fun b =>
      pg 8 (mask 8) (S j) (mulCK ET a b) ==
        mulCK ET (pg 8 (mask 8) (S j) a) (pg 8 (mask 8) (S j) b)) &&
    (List.range 128).all fun a => (List.range 128).any fun b => pg 8 (mask 8) (S j) b == a

end CFSG.KC.W16Pg

end
