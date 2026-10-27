module

public import Certificates.Data.GMS78RuCzEnum
public import Certificates.Data.GMS78RuNModel
public import Certificates.Data.GMS78RuAsmData
public import CFSG.Certificates.CentralizerRelations

public section

namespace CFSG.ComponentClassification.GMS78.RuCz

open CFSG.CosetTable CFSG.GMS78Ru CFSG.GMS78RuSim CFSG.GMS78RuQ CFSG.GMS78RuN
  CFSG.ComponentClassification.GMS78.RuAsm

@[expose] def czmV0 : List ℕ := [0, 16, 32, 48]

@[expose] def czmX0 : List NTrip :=
  czmV0.flatMap fun m => (List.finRange 8).map fun t => (m, t, linId)

@[expose] def czmZ0 : NTrip := (0, 4, linId)

@[expose] def czmInX0 (y : NTrip) : Bool := czmV0.contains y.1 && y.2.2 == linId

@[expose] def czmConj (g gi x : NTrip) : NTrip := nMulT (nMulT g x) gi

@[expose] def czmSame (y y' : NTrip) : Bool := y == y' || y == nMulT y' czmZ0

@[expose] def czmConjW (w : List (Fin 7 × Bool)) (x : NTrip) : NTrip :=
  czmConj (nEvalW w) (nEvalW (FreeGroup.invRev w)) x

@[expose] def czmRepCodes : List (List ℕ) :=
  [[], [0], [6], [8], [9], [0, 6], [0, 8], [0, 9], [6, 8], [6, 9], [8, 0], [8, 6], [8, 8], [9, 0],
   [9, 6], [0, 6, 8], [0, 6, 9], [0, 8, 0], [0, 8, 6], [0, 8, 8], [0, 9, 0], [0, 9, 6], [6, 8, 8],
   [0, 6, 8, 8]]

@[expose] def czmRep (i : ℕ) : List (Fin 7 × Bool) := wordOfCodes 7 (czmRepCodes.getD i [])

@[expose] def czmJWord (i : ℕ) : List (Fin 7 × Bool) := wordOfCodes 7 (czL10Codes.getD i [])

@[expose] def czmZ0Check : Bool := nEvalW ruZ0Word == czmZ0

@[expose] def czmLetterCheck : Bool :=
  (List.range 5).all fun i =>
    nMulT (nImg.getD i nOneT) czmZ0 == nMulT czmZ0 (nImg.getD i nOneT) &&
    czmX0.all fun x => czmInX0 (czmConj (nImg.getD i nOneT) (nImgInv.getD i nOneT) x) &&
      czmInX0 (czmConj (nImgInv.getD i nOneT) (nImg.getD i nOneT) x)

@[expose] def czmJCheck : Bool :=
  (List.range 6).all fun i => czmX0.all fun x => czmSame (czmConjW (czmJWord i) x) x

@[expose] def czmRepCheck : Bool :=
  (List.range 24).all fun i => (List.range 24).all fun j =>
    !decide (i < j) || czmX0.any fun x => !czmSame (czmConjW (czmRep i) x) (czmConjW (czmRep j) x)

@[expose] def czmConjCode (c r : Lin8) : Lin8 := linComp (linComp c r) (linInv c)

@[expose] def czmInvolCheck : Bool :=
  glList.all fun r => !(linComp r r == linId && r != linId) ||
    decide (9 ≤ (glList.map fun c => czmConjCode c r).dedup.length)

end CFSG.ComponentClassification.GMS78.RuCz
