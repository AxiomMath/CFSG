module

public import CFSG.Sporadic.FischerOddCore.Fi24R2Data
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.Sporadic.FischerOddCore

open CFSG.Monster.B.Co2.Native

@[expose] def mulTree (n : Nat) (gens : Array (Array Nat)) (par lab : Array Nat) :
    Array (Array Nat) :=
  (List.range (par.size - 1)).foldl
    (fun E i => E.push (compA n gens[lab[i + 1]!]! E[par[i + 1]!]!)) #[idA n]

@[expose] def fi22SylParText : String := include_str "Fi22SylPar.txt"
@[expose] def fi22SylLabText : String := include_str "Fi22SylLab.txt"
@[expose] def fi22SylNxtText : String := include_str "Fi22SylNxt.txt"
@[expose] def fi22SylCovWText : String := include_str "Fi22SylCovW.txt"
@[expose] def fi22SylCovSText : String := include_str "Fi22SylCovS.txt"
@[expose] def fi22SylCovJText : String := include_str "Fi22SylCovJ.txt"

@[expose] def fi22SylSizes : List Nat := [27, 81, 5, 81, 5, 729, 25, 7, 81, 5, 7]
@[expose] def fi22SylOffs : List Nat := [0, 27, 108, 113, 194, 199, 928, 953, 960, 1041, 1046]
@[expose] def fi22SylNxtSizes : List Nat := [162, 648, 10, 810, 10, 8748, 100, 14, 486, 10, 14]
@[expose] def fi22SylNxtOffs : List Nat :=
  [0, 162, 810, 820, 1630, 1640, 10388, 10488, 10502, 10988, 10998]

@[expose] def fi22SylField (d : Nat) (t : String) (o m : Nat) : Array Nat :=
  (hexNums d t).extract o (o + m)

@[expose] def fi22SylPar (s : Nat) : Array Nat :=
  fi22SylField 3 fi22SylParText (fi22SylOffs.getD s 0) (fi22SylSizes.getD s 0)

@[expose] def fi22SylLab (s : Nat) : Array Nat :=
  fi22SylField 1 fi22SylLabText (fi22SylOffs.getD s 0) (fi22SylSizes.getD s 0)

@[expose] def fi22SylNxt (s : Nat) : Array Nat :=
  fi22SylField 3 fi22SylNxtText (fi22SylNxtOffs.getD s 0) (fi22SylNxtSizes.getD s 0)

@[expose] def fi22SylCov (s : Nat) : Array (Nat × Nat × Nat) :=
  let o := fi22SylOffs.getD s 0
  let m := fi22SylSizes.getD s 0
  let w := fi22SylField 2 fi22SylCovWText o m
  let t := fi22SylField 3 fi22SylCovSText o m
  let j := fi22SylField 1 fi22SylCovJText o m
  Array.ofFn (n := m) fun i => (w[i.val]!, t[i.val]!, j[i.val]!)

end CFSG.Sporadic.FischerOddCore

end
