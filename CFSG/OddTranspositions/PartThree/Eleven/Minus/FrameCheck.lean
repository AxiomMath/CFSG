module

public import CFSG.OddTranspositions.PartThree.Eleven.Minus.FrameData
public import CFSG.RankThree.Native.PermEnumeration

public section

namespace CFSG.OddTranspositions.PartThree.MinusFrame

open CFSG.OddTranspositions.PartThree
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native

@[expose] def isFrame (p : ℕ) : Bool := (List.finRange 3).any fun i => frameArr[(i : ℕ)]! == p

@[expose] def tArr (_ : Unit := ()) : Array ℕ :=
  compA 65 (compA 65 minusTable[frameArr[0]!]! minusTable[frameArr[1]!]!)
    minusTable[frameArr[2]!]!

@[expose] def commutesA (a b : Array ℕ) : Bool := eqA 65 (compA 65 a b) (compA 65 b a)

@[expose] def t0Cert (_ : Unit := ()) : ArrCert := enumBfs 65 t0Gens minusBase 32

@[expose] def t0Check (c : ArrCert) : Bool := enumOK 65 t0Gens minusBase c && (c.pts.size == 16)

@[expose] def t0SubCheck (E : ArrCert) : Bool :=
  (List.range t0Gens.size).all fun k => E.pts.toList.any (eqA 65 t0Gens[k]!)

@[expose] def frameMemCheck (c : ArrCert) : Bool :=
  (List.range 65).all fun k =>
    (c.pts.toList.any (eqA 65 minusTable[k]!)) == isFrame k

@[expose] def frameCommuteCheck (_ : Unit := ()) : Bool :=
  (List.finRange 3).all fun i => (List.finRange 3).all fun j =>
    (minusTable[frameArr[(i : ℕ)]!]!)[frameArr[(j : ℕ)]!]! == frameArr[(j : ℕ)]!

@[expose] def centCheck (_ : Unit := ()) : Bool :=
  let t := tArr ()
  (List.range 65).all fun k =>
    commutesA t (minusTable[k]!) == (centArr.toList.any fun j => j == k)

@[expose] def l0Cert (_ : Unit := ()) : ArrCert := enumBfs 65 l0Gens minusBase 130

@[expose] def l0Check (_ : Unit := ()) : Bool :=
  let c := l0Cert ()
  enumOK 65 l0Gens minusBase c && (c.pts.size == 120) &&
    (List.finRange 15).all fun a => (List.finRange 15).all fun b =>
      c.pts.toList.any fun g => g[centArr[(a : ℕ)]!]! == centArr[(b : ℕ)]!

@[expose] def aCert (_ : Unit := ()) : ArrCert := enumBfs 65 aGens minusBase 65

@[expose] def aCheck (_ : Unit := ()) : Bool :=
  let c := aCert ()
  let lc := l0Cert ()
  let t := tArr ()
  enumOK 65 aGens minusBase c && (c.pts.size == 60) &&
    c.pts.toList.all (fun g => !(eqA 65 g t)) &&
    (aGens.toList.all fun a => lc.pts.toList.any (eqA 65 a)) &&
    conjSimpleOK 65 minusBase c

@[expose] def stabCheck (E : ArrCert) : Bool :=
  let t := tArr ()
  allLt E.pts.size fun k =>
    let g := E.pts[k]!
    !((List.finRange 15).all fun i => g[centArr[(i : ℕ)]!]! == centArr[(i : ℕ)]!) ||
      eqA 65 g (idA 65) || eqA 65 g t

@[expose] def cardCentralCheck (E : ArrCert) : Bool :=
  let t := tArr ()
  (E.pts.toList.filter fun g => commutesA g t).length == 240

@[expose] def notMemCheck (_ : Unit := ()) : Bool :=
  let t := tArr ()
  (List.range 65).all fun k => !(eqA 65 t minusTable[k]!)

@[expose] def notMulCheck (_ : Unit := ()) : Bool :=
  let t := tArr ()
  (List.finRange 15).all fun a => (List.finRange 15).all fun b =>
    !(eqA 65 (compA 65 minusTable[centArr[(a : ℕ)]!]! minusTable[centArr[(b : ℕ)]!]!) t)

@[expose] def conjCommuteCheck (E : ArrCert) : Bool :=
  let t := tArr ()
  let y := compA 65 (compA 65 xArr t) (invCand 65 xArr)
  validA 65 xArr && !(eqA 65 y t) && commutesA t y && E.pts.toList.any (eqA 65 xArr)

@[expose] def frameCheck (_ : Unit := ()) : Bool :=
  let c := t0Cert ()
  let E := minusEnum ()
  t0Check c && t0SubCheck E && frameMemCheck c && frameCommuteCheck () && centCheck () &&
    l0Check () && aCheck () && stabCheck E && cardCentralCheck E && notMemCheck () &&
    notMulCheck () && conjCommuteCheck E

end CFSG.OddTranspositions.PartThree.MinusFrame
