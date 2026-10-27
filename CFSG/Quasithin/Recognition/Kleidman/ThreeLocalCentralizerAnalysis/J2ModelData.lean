module

public import Certificates.Data.CFSGNative.J2.Certificate
public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.Presentation

public section

namespace CFSG.Quasithin.Kleidman.ThreeLocal.J2Model

open CFSG.Sporadic.Th.Native
open CFSG.Sporadic.J1.Native (genTables)
open CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition (j3WordsRest)

@[expose] def wFour : List (Fin 7 × Bool) :=
  [(5, true), (6, true), (5, false), (6, false), (3, true), (5, true), (6, true), (5, false), (6, false), (3, true), (5, true), (6, true), (5, false), (6, false), (3, true), (5, true), (6, true), (5, false), (6, false), (3, true)]

@[expose] def j2Rels : List (List (Fin 7 × Bool)) := j3WordsRest ++ [wFour]

@[expose] def uWord2 : ℕ → List ℤ
  | 0 => [2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2]
  | 1 => [1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2]
  | 2 => [1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2]
  | 3 => [1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2]
  | 4 => [1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1]
  | 5 => [1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1]
  | 6 => [1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1]
  | _ => []

@[expose] def wa7 : List ℤ := [5, 6, -7, -5, 1, 6, 5, 7, 6, -5]

@[expose] def wb7 : List ℤ := [3, -5, 6, 7, 6, -5, -7, 6, -7]

@[expose] def fWord : List (Fin 7 × Bool) := [(6, true), (5, true), (6, true), (5, true)]

@[expose] def tauWord : List (Fin 7 × Bool) := [(1, true), (6, true), (4, false), (5, true), (6, false), (4, true)]

@[expose] def tau2Word : List (Fin 7 × Bool) := [(4, true), (6, false), (4, true), (5, true), (4, false), (6, true), (4, false)]

@[expose] def encodeWord (r : List (Fin 7 × Bool)) : List ℤ :=
  r.map fun x => if x.2 then (x.1.val : ℤ) + 1 else -((x.1.val : ℤ) + 1)

@[expose] def uTab2 (n : ℕ) (gen : ℤ → Table) (k : ℕ) : Table := wordT n gen (uWord2 k)

@[expose] def letTab (Tu Tui : Array Table) (z : ℤ) : Table :=
  if 0 < z then Tu[(z - 1).toNat]! else Tui[(-z - 1).toNat]!

@[expose] def movesSome (n : ℕ) (T : Table) : Bool := (List.range n).any fun i => ap T i != i

@[expose] def differSome (n : ℕ) (T U : Table) : Bool := (List.range n).any fun i => ap T i != ap U i

@[expose] def modelTu (n : ℕ) (gen : ℤ → Table) : Array Table := (Array.range 7).map (uTab2 n gen)

@[expose] def modelTui (n : ℕ) (gen : ℤ → Table) : Array Table := (modelTu n gen).map (invT n)

@[expose] def modelCheckAt (n : ℕ) (gen : ℤ → Table) : Bool :=
  let Tu := modelTu n gen
  let Tui := modelTui n gen
  let L := letTab Tu Tui
  let tf := wordT n L (encodeWord fWord)
  let tt := wordT n L (encodeWord tauWord)
  let tt' := wordT n L (encodeWord tau2Word)
  (List.range 7).all (fun k => invOK n Tu[k]! Tui[k]!) &&
    j2Rels.all (fun r => wordT n L (encodeWord r) == idT n) &&
    wordT n L wa7 == gen 1 && wordT n L wb7 == gen 2 &&
    compT n tt tt == idT n && compT n tt' tt' == idT n &&
    compT n tt tt' == compT n tt' tt && movesSome n tt && movesSome n tt' && differSome n tt tt' &&
    powT n 5 tf == idT n && movesSome n tf &&
    compT n tf tt == compT n tt tf && compT n tf tt' == compT n tt' tf

@[expose] def j2ModelCheck : Bool :=
  let O := CFSG.Sporadic.J2.Native.orbitData ()
  decide (O.pts.size = 315) && modelCheckAt 315 (genTables O)

end CFSG.Quasithin.Kleidman.ThreeLocal.J2Model
