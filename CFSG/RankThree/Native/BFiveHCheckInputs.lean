module

public import Certificates.Data.CFSGNative.MonsterB.Primes
public meta import Certificates.Data.CFSGNative.MonsterB.Primes

public section

namespace CFSG.RankThree.Native

open CFSG.Monster.B.Bin CFSG.Monster.B.Primes.Native

@[expose] def bFiveHRows : List (List Nat) :=
  [[0, 1, 0, 0], [3, 1, 1, 0], [2, 2, 2, 0], [1, 1, 1, 4]]

@[expose] def bFiveHC : List Nat := [0, 1, 2, 2]

@[expose] def bFiveHChecks (n : Nat) (A B : Mat) (Hr : List (List Nat)) (hc : List Nat) : Bool :=
  let R := regRun n 22 fiveProg A B
  let x := R.1.getD 1 #[]
  let h := R.1.getD 2 #[]
  let xi := powM n x 4
  let hi := powM n h 7
  let w := mulP n x (powM n h 3)
  let q1 := powM n w 8
  let q2 := mulP n (mulP n hi q1) h
  let q3 := mulP n (mulP n xi q1) x
  let q4 := mulP n (mulP n xi q2) x
  let qs := [q1, q2, q3, q4]
  let z := mulP n (mulP n (mulP n (powM n q1 4) (powM n q2 4)) q1) q2
  let Z := powTable n 5 z
  let T := qs.map (powTable n 5)
  R.2 && actOK n qs T Z h hi Hr hc && conjM n z h hi == mulP n z z

end CFSG.RankThree.Native
