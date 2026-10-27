module

public import Certificates.Data.U43Model

public section

namespace CFSG.KGroups.U43

open CFSG.Monster.B.Co2.Native CFSG.KGroups.Native

@[expose] def sevenWord : Word := [(1, true), (0, true)]

@[expose] def commuteArr (n : Nat) (s t : Array Nat) : Bool :=
  eqA n (compA n s t) (compA n t s)

@[expose] def conjugateA (n : Nat) (x xi e : Array Nat) : Array Nat :=
  compA n x (compA n e xi)

@[expose] def noSevenCheck (n : Nat) (tA tB : Array Nat) : Bool :=
  let G := genAB tA tB
  let Gi := invArrs n G
  let x := wArr n tA tB sevenWord
  let xi := invCand n x
  let x2 := compA n x x
  let xi2 := compA n xi xi
  let L := (orbRec n tA tB).L
  invsOK n G Gi && eqA n (compA n tA tA) (idA n) && isInvA n x xi &&
    eqA n (compA n x2 (compA n x2 (compA n x2 x))) (idA n) && !eqA n x (idA n) &&
    allLt 2835 fun i =>
      !(commuteArr n L[i]! (conjugateA n x xi L[i]!) &&
        commuteArr n L[i]! (conjugateA n x2 xi2 L[i]!))

end CFSG.KGroups.U43
