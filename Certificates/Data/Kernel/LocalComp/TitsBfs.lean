module

public import Certificates.Data.Kernel.LocalComp.TitsChain

public noncomputable section

namespace CFSG.KC.LocalComp.TitsChain

open CFSG.KC.Enum CFSG.KS

@[expose] def keyK (TT : Nat → Nat → Nat) (ls : List Nat) (i k : Nat) : Nat :=
  Nat.add (Nat.mul 32 (f16 (TT i k) 1)) (ls.idxOf (f16 (TT i k) 2))

@[expose] def bfsOK (TL : Nat → Nat) (TT TS : Nat → Nat → Nat) (sz : Nat → Nat) (CP : List Nat)
    (i : Nat) : Bool :=
  let ls := levLetters TL CP i
  bAnd(allN (Nat.sub (sz i) 2) (fun k =>
      Nat.blt (keyK TT ls i (Nat.succ k)) (keyK TT ls i (Nat.succ (Nat.succ k)))),
    allN (sz i) fun h => allN ls.length fun u =>
      strictB (f16 (TS i (apL TL (ls.getD u 0) (f16 (TT i h) 0))) 0) fun j =>
        bIf(Nat.beq j 0, true, Nat.ble (keyK TT ls i j) (Nat.add (Nat.mul 32 h) u)))

@[expose] def depthK (TT : Nat → Nat → Nat) (i : Nat) : Nat → Nat → Bool
  | 0, k => Nat.beq k 0
  | f + 1, k => bIf(Nat.beq k 0, true, depthK TT i f (f16 (TT i k) 1))

@[expose] def depthOK (TT : Nat → Nat → Nat) (sz : Nat → Nat) (i : Nat) : Bool :=
  allN (sz i) fun k => depthK TT i 64 k

end CFSG.KC.LocalComp.TitsChain

end
