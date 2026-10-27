module

public import Certificates.Data.Kernel.KDense.Twins
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.Rep4371Row

open CFSG.KC CFSG.KC.KDense CFSG.KC.Loop

@[expose] noncomputable def enc (s η c : Nat) : Nat := Nat.add s (Nat.add (Nat.mul 2 η) (Nat.mul 4 c))

@[expose] noncomputable def pi0T (c : Nat) : Nat := Nat.xor c (selB (bitN c 0) (nat_lit 63))

@[expose] noncomputable def shiftT (a c : Nat) : Nat := pi0T (Nat.xor c a)

@[expose] noncomputable def kT (a c : Nat) : Nat :=
  Nat.land (Nat.shiftRight (popc24 (Nat.land (wordT a) (wordT c))) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def eYT (a η c : Nat) : Nat :=
  strictN (pi0T c) fun p =>
    nIf(Nat.beq η 1, enc (kT a p) 1 p, enc (pairT a (thetaT p)) 0 (shiftT a p))

@[expose] noncomputable def ePermT (P BT K η c : Nat) : Nat :=
  strictN (pi0T c) fun p => strictN (permCT P p) fun pc =>
    enc (Nat.xor (kappaT BT p) (Nat.land (Nat.xor η K) (bitN pc 0))) (Nat.xor η K) (pi0T pc)

@[expose] noncomputable def ePauliT (s a d η c : Nat) : Nat :=
  strictN (shiftT a (pi0T c)) fun c' =>
    enc (Nat.xor (Nat.xor s (Nat.land η (bitN a 0))) (pairT c' d)) (Nat.xor η (pairT 63 d)) c'

@[expose] noncomputable def thenT (f : Nat → Nat → Nat) (r : Nat) : Nat :=
  strictN r fun r0 => Nat.xor (f (bitN r0 1) (Nat.shiftRight r0 2)) (Nat.land r0 1)

@[expose] noncomputable def sigT (A P BT K η c : Nat) : Nat := thenT (ePermT P BT K) (eYT A η c)

@[expose] noncomputable def sqT (A P BT K η c : Nat) : Nat := thenT (sigT A P BT K) (sigT A P BT K η c)

@[expose] noncomputable def sqRowsT (A P BT K s a d : Nat) : Bool :=
  allBelow 2048 32 fun q => (fun c => bAnd(Nat.beq (sqT A P BT K 0 c) (ePauliT s a d 0 c),
    Nat.beq (sqT A P BT K 1 c) (ePauliT s a d 1 c))) (Nat.mul 2 q)

end CFSG.KC.Rep4371Row

end
