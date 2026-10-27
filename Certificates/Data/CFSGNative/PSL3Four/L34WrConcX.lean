module

public import Certificates.Data.CFSGNative.PSL3Four.L34RA

public section

namespace CFSG.PSL3Four.Native

abbrev WIdx : Type := Fin 256 × Fin 256 × Bool

@[expose] def rmul (M : Array Nat) (i j : Fin 256) : Fin 256 :=
  ⟨M[256 * i.val + j.val]! % 256, Nat.mod_lt _ (by decide)⟩

@[expose] def rinv (V : Array Nat) (i : Fin 256) : Fin 256 :=
  ⟨V[i.val]! % 256, Nat.mod_lt _ (by decide)⟩

@[expose] def wmul (M : Array Nat) (p q : WIdx) : WIdx :=
  if q.2.2 then (rmul M p.2.1 q.1, rmul M p.1 q.2.1, xor p.2.2 q.2.2)
  else (rmul M p.1 q.1, rmul M p.2.1 q.2.1, xor p.2.2 q.2.2)

@[expose] def wone : WIdx := (0, 0, false)

@[expose] def wIsA (M : Array Nat) (p : WIdx) : Bool :=
  !p.2.2 && wmul M p p == wone &&
    ((p.1 == 0 && p.2.1 != 0 && labSBits.testBit p.2.1.val) ||
      (p.2.1 == 0 && p.1 != 0 && labSBits.testBit p.1.val))

@[expose] def wIsD (M : Array Nat) (p : WIdx) : Bool :=
  !p.2.2 && wmul M p p == wone && p.1 != 0 && p.2.1 != 0 && labSBits.testBit p.1.val &&
    labSBits.testBit p.2.1.val

@[expose] def wIsUU (M : Array Nat) (p : WIdx) : Bool :=
  !p.2.2 && wmul M p p == wone && labUniBits.testBit p.1.val && labUniBits.testBit p.2.1.val

@[expose] def wcos (M : Array Nat) (r5 r6 : Fin 256) (i : Fin 256) : Fin 4 :=
  if labT0Bits.testBit i.val then 0 else
    if labT0Bits.testBit (rmul M r5 i).val then 1 else
      if labT0Bits.testBit (rmul M r6 i).val then 2 else 3

@[expose] def wcc (M : Array Nat) (r5 r6 : Fin 256) (p : WIdx) : Fin 4 × Fin 4 × Bool :=
  (wcos M r5 r6 p.1, wcos M r5 r6 p.2.1, p.2.2)

@[expose] def allIdx (_ : Unit := ()) : List WIdx :=
  (List.finRange 256).flatMap fun i =>
    (List.finRange 256).flatMap fun j => [(i, j, false), (i, j, true)]

@[expose] def wX (M : Array Nat) (r5 r6 : Fin 256) (U : List (Fin 4 × Fin 4 × Bool)) :
    List WIdx :=
  (allIdx ()).filter fun p => U.contains (wcc M r5 r6 p)

@[expose] def wComm (M : Array Nat) (p q : WIdx) : Bool := wmul M p q == wmul M q p

@[expose] def wSqOK (M : Array Nat) (a z : WIdx) : Bool :=
  z == a || (wIsA M z && wIsD M (wmul M a z)) || (wIsD M z && wIsA M (wmul M a z))

@[expose] def chkD (M : Array Nat) (X : List WIdx) : Bool :=
  X.any fun d => wIsD M d && X.all fun x => wComm M x d

@[expose] def chkSwap (M : Array Nat) (X : List WIdx) : Bool :=
  (X.any fun h => h.2.2 && wmul M (wmul M h h) (wmul M h h) == wone) &&
    X.all fun g => !g.2.2 ||
      (wmul M g g != wone && wmul M g (wmul M g g) != wone &&
        (wmul M (wmul M g g) (wmul M g g) != wone || wIsUU M (wmul M g g)))

@[expose] def chkInv (M : Array Nat) (X : List WIdx) : Bool :=
  X.all fun p => wmul M p p != wone || p == wone || wIsA M p || wIsD M p || wIsUU M p

@[expose] def chkA (M : Array Nat) (X : List WIdx) : Bool :=
  X.all fun b => !wIsA M b ||
    ((X.any fun x => wmul M x b != wmul M b x) &&
      decide (1024 ≤ (X.filter fun x => wComm M x b).length))

@[expose] def pairOK (M : Array Nat) (a : WIdx) (C : List WIdx) : Bool :=
  decide (C.length ≤ 128) && decide ((C.filter fun x => wmul M x x == wone).length < 16) &&
    C.all fun x => wmul M x x == wone || wSqOK M a (wmul M x x)

@[expose] def chkPairWith (M : Array Nat) (a : WIdx) (Ca : List WIdx) : Bool :=
  Ca.all fun y => !wIsUU M y || pairOK M a (Ca.filter fun x => wComm M x y)

@[expose] def chkPair (M : Array Nat) (X : List WIdx) : Bool :=
  X.all fun a => !wIsA M a || chkPairWith M a (X.filter fun x => wComm M x a)

@[expose] def chkAll (M : Array Nat) (X : List WIdx) : Bool :=
  chkD M X && chkSwap M X && chkInv M X && chkA M X && chkPair M X

@[expose] def concXCheck (U : List (Fin 4 × Fin 4 × Bool)) : Bool :=
  let M := raMulTab ()
  let V := raInvTab ()
  chkAll M (wX M (rinv V 5) (rinv V 6) U)

end CFSG.PSL3Four.Native
