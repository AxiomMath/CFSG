module

public import Certificates.Data.Kernel.AE6Tri.Defs
public import Certificates.Data.Kernel.ExactGen.Parse

public section

namespace CFSG.KC.AE6Core

open CFSG.KC.Enum CFSG.KS CFSG.KC.YoshQ CFSG.KC.AE6F CFSG.KC.AE6Tri CFSG.KC.ExactGen
  Certificates.AE6Model

@[expose] def piecesL (cs : List Char) : List (List (List Char)) :=
  ((cs.filter fun c => !isWs c).splitOn ';').map fun w =>
    (w.splitOn ',').filter fun p => !p.isEmpty

@[expose] def wordsL (cs : List Char) : List (List Int) := (piecesL cs).map (List.map intOfL)

@[expose] def toksOKw (cs : List Char) : Bool := (piecesL cs).all fun w => w.all tokOK

@[expose] def cwN (cs : List Char) : List (List Nat) :=
  (wordsL cs).map (List.map fun z => z.natAbs - 1)

@[expose] noncomputable def invOKN (G : List Nat) : Bool :=
  G.all fun g => eqN 360 9 (pmN 360 9 g g) (pidn 360 9)

@[expose] noncomputable def commAllN (G : List Nat) (zw : List Nat) (C : List (List Nat)) : Bool :=
  strictB (awN G zw) fun Z => allIx C (fun _ c => strictB (awN G c) fun X =>
    eqN 360 9 (pmN 360 9 X Z) (pmN 360 9 Z X)) 0

@[expose] noncomputable def plOK (G : List Nat) (C : List (List Nat)) (PS : Nat → Nat) : Bool :=
  allIx C (fun i c => strictB (awN G c) fun X => strictB (invN 360 9 X) fun XI =>
    allIx kWords (fun t x =>
      Nat.beq (PS (Nat.add (Nat.mul 2 i) t)) (pmN 360 9 (pmN 360 9 X (awN G x)) XI)) 0) 0

end CFSG.KC.AE6Core

end
