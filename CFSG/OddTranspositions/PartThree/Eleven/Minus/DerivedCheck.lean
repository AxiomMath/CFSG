module

public import CFSG.OddTranspositions.PartThree.Eleven.Minus.DerivedData
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutClass
public import Mathlib

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four.Native CFSG.QuasithinUnique.Id2519.HSAut

@[expose] def minusLGensCheck (_ : Unit := ()) : Bool :=
  (minusLGens.size == 5) &&
    allLt 5 (fun k => validA 65 minusLGens[k]!) &&
    eqA 65 minusLGens[0]! (compA 65 minusTable[0]! minusTable[1]!) &&
    eqA 65 minusLGens[1]! (compA 65 minusTable[0]! minusTable[3]!) &&
    eqA 65 minusLGens[2]! (compA 65 minusTable[0]! minusTable[4]!) &&
    eqA 65 minusLGens[3]! (compA 65 minusTable[0]! minusTable[10]!) &&
    eqA 65 minusLGens[4]! (compA 65 minusTable[0]! minusTable[11]!)

@[expose] def minusLEnumCheck (E : ArrCert) : Bool :=
  enumOK 65 minusLGens minusBase E && (E.pts.size == 7800)

@[expose] def minusLSizeCheck (E : ArrCert) : Bool :=
  allLt E.pts.size fun i => (E.pts[i]!).size == 65

@[expose] def minusLReflCheck (E : ArrCert) : Bool :=
  allLt E.pts.size fun j => allLt 65 fun i => !(eqA 65 E.pts[j]! minusTable[i]!)

@[expose] def minusLCentralCheck (M : ArrCert) : Bool :=
  allLt M.pts.size fun i =>
    !(allLt minusLGens.size fun k =>
        eqA 65 (compA 65 M.pts[i]! minusLGens[k]!) (compA 65 minusLGens[k]! M.pts[i]!)) ||
      eqA 65 M.pts[i]! (idA 65)

@[expose] def minusLTransCheck (M : ArrCert) : Bool :=
  allLt 65 fun i => (List.range M.pts.size).any fun j => (M.pts[j]!)[0]! == i

@[expose] def minusLLocalCheck (E : ArrCert) : Bool :=
  E.pts.toList.any (eqA 65 minusSylowA) && E.pts.toList.any (eqA 65 minusSylowB) &&
    E.pts.toList.any (eqA 65 minusA5Gens[0]!) && E.pts.toList.any (eqA 65 minusA5Gens[1]!) &&
    validA 65 minusSylowA && validA 65 minusSylowB &&
    validA 65 minusA5Gens[0]! && validA 65 minusA5Gens[1]!

@[expose] def minusDerivedCheck (_ : Unit := ()) : Bool :=
  let E := minusLEnum ()
  let M := minusEnum ()
  minusLGensCheck () && minusLEnumCheck E && minusLSizeCheck E && minusLReflCheck E &&
    minusLCentralCheck M && minusLTransCheck M && minusLLocalCheck E

end CFSG.OddTranspositions.PartThree
