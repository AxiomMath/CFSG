module

public import CFSG.Certificates.Kernel.Common.Loop
public import CFSG.Certificates.Kernel.Enum.Defs
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchKillData
public import Mathlib.Data.Nat.Bitwise

public section

namespace CFSG.KC.SBCen

open CFSG.KC.Enum CFSG.EvenSmallLie.OmegaEight.SpBranch

@[expose] noncomputable def cmL (mul : Nat → Nat → Nat) (c : Nat) (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun q _ ih => Nat.add (nIf(Nat.beq (mul c q) (mul q c), 1, 0)) (Nat.shiftLeft ih 20)) L

@[expose] noncomputable def rowF (mul : Nat → Nat → Nat) (nfE nfA : Nat → Nat) (W L x : Nat) : Nat :=
  mul fld(W, Nat.mul 16 (nfE x), 65535) fld(L, Nat.mul 16 (nfA x), 65535)

@[expose] noncomputable def extMulF (N : Nat) (mul : Nat → Nat → Nat) (F : Nat → Nat) (z c d : Nat) :
    Nat :=
  nIf(Nat.blt c N,
    nIf(Nat.blt d N, mul c d, Nat.add (mul c (Nat.sub d N)) N),
    nIf(Nat.blt d N, Nat.add (mul (Nat.sub c N) (F d)) N,
      mul (mul (Nat.sub c N) (F (Nat.sub d N))) z))

@[expose] noncomputable def cen (mul : Nat → Nat → Nat) (Q U : List Nat) (nQ c : Nat) : Nat :=
  strictN (mul c c) fun s =>
    nIf(Nat.beq s 0, nIf(Nat.beq c 0, 0, Nat.add 1 (Nat.shiftLeft (cmL mul c Q) 20)),
      nIf(Nat.beq (mul s s) 0, Nat.shiftLeft (cmL mul c U) (Nat.mul 20 (Nat.succ nQ)), 0))

@[expose] noncomputable def cenBlk (mul : Nat → Nat → Nat) (Q U : List Nat) (nQ a : Nat) : Nat :=
  CFSG.KC.Loop.sumBelow 8192 128 fun i => cen mul Q U nQ (Nat.add a i)

@[expose] noncomputable def cenLane (T j : Nat) : Nat := fld(T, Nat.mul 20 j, 1048575)

variable (mul : ℕ → ℕ → ℕ) (inv : ℕ → ℕ) (gens : List ℕ) (N : ℕ)

@[expose] def killG (cI : ℕ → ℕ) (R : List ℕ) (cO : ℕ → ℕ) (m : ℕ) (χ : ℕ → Bool) (n5 : Bool)
    (t : ℕ) (ti : ℕ × ℕ) : Bool :=
  orbClosed mul inv gens t (kRec mul inv gens m t) && (kRec mul inv gens m t).length == m &&
    orbOK mul inv N t (kRec mul inv gens m t) &&
    cI t == ti.1 && cO t == ti.2 && χ t &&
    R.all fun r => !(cI r == ti.1) ||
      (if n5 then (kRec mul inv gens m t).any fun p => p.1 == r else χ r) ||
      !(cO r == ti.2)

@[expose] def queriedG (cI : ℕ → ℕ) (R : List ℕ) (m : ℕ) (χ : ℕ → Bool) (n5 : Bool) (t : ℕ)
    (ti : ℕ × ℕ) (U : List ℕ) : Bool :=
  U.contains t && R.all fun r => !(cI r == ti.1) ||
    (if n5 then (kRec mul inv gens m t).any fun p => p.1 == r else χ r) || U.contains r

end CFSG.KC.SBCen

end
