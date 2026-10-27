module

public import CFSG.RankThree.PartOne.K133Spor.HSPairInputs
public import CFSG.Sporadic.HNOddCore.QCheckInputs

public section

namespace CFSG.RankThree.PartOne.K133Spor

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native

@[expose] def isFiveA (n : ℕ) (f : Array ℕ) : Bool :=
  eqA n (powA5 n f) (idA n) && !eqA n f (idA n)

@[expose] def isTwoA (n : ℕ) (u : Array ℕ) : Bool :=
  eqA n (compA n u u) (idA n) && !eqA n u (idA n)

@[expose] def commA (n : ℕ) (a b : Array ℕ) : Bool :=
  allLt n fun i => a[b[i]!]! == b[a[i]!]!

@[expose] def fixFreeA (n : ℕ) (a b : Array ℕ) : Bool :=
  allLt n fun m => m == 0 || !(a[m]! == m && b[m]! == m)

@[expose] def gbarCheck (n : ℕ) (pts : Array (Array ℕ)) : Bool :=
  let fives := pts.filter (isFiveA n)
  let twos := pts.filter (isTwoA n)
  (twos.all fun u =>
      let fu := fives.filter fun a => commA n u a
      fu.all fun a => fu.all fun b => !commA n a b || memLineA n a b) &&
    fives.all fun a => fives.all fun b =>
      fixFreeA n a b || !commA n a b || memLineA n a b

@[expose] def gbarKeys : List ℕ := [4, 1, 8, 16]

@[expose] def gbarCert : ArrCert :=
  enumBfs 256 CFSG.Sporadic.HNOddCore.Native.colPerms gbarKeys 14401

abbrev GBarOK : Prop :=
  (enumOK 256 CFSG.Sporadic.HNOddCore.Native.colPerms gbarKeys gbarCert &&
    gbarCheck 256 gbarCert.pts) = true

end CFSG.RankThree.PartOne.K133Spor
