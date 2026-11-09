module

public import Certificates.Data.Kernel.SporLatDcT
public import Certificates.Data.Kernel.SporLatDcTup

public section

namespace CFSG.KC.SLDc

open CFSG.QuasithinUnique.Ch1.SporLat

@[expose] noncomputable def otActRc (w : Nat) (Ps : List Nat) (lbl rows : List (List Nat)) : Bool :=
  Nat.ble Ps.length rows.length &&
    allIdxRc (fun l row => Nat.beq row.length lbl.length &&
      zipAllRc (fun a x => Nat.blt a lbl.length &&
        eqLRc (lbl.getD a []) (mapRc (CFSG.KC.LQT.PW.imgW w (Ps.getD l 0)) x)) row lbl) 0 rows

@[expose] noncomputable def otIdxR (w m : Nat) (Ps : List Nat) (O : OmegaData (List Nat)) : Bool :=
  decide (O.lbl.toList.getD 0 default = List.range m) && decide (0 < O.lbl.toList.length) &&
    otActRc w Ps O.lbl.toList (O.pn.toList.map Array.toList) &&
    (List.range O.lbl.toList.length).all (fun i => i == 0 ||
      (decide (O.par.toList.getD i default < i) && decide (O.via.toList.getD i default < Ps.length) &&
        (O.pn.toList.getD (O.via.toList.getD i default) default).toList.getD
          (O.par.toList.getD i default) default == i)) &&
    decide O.lbl.toList.Nodup

@[expose] noncomputable def wordFR (L : Nat → Nat → Nat) (w : List Nat) (p : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) p (fun l _ ih => L l ih) w

@[expose] noncomputable def wordER (L : Nat → Nat → Nat) (E : List (List Nat)) (u : List Nat)
    (p : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) p (fun i _ ih => wordFR L (E.getD i []) ih) u

section Checks

variable (C : DcCtx) (D : DcData)

@[expose] noncomputable def genLabR (g : List Nat) : List Nat :=
  insNRc (mapRc (wordFR C.L g) C.Δ)

@[expose] noncomputable def memWR (E : List (List Nat)) (x : Wit) (T : List Nat) : Bool :=
  allRc (fun i => Nat.blt i E.length) x.1 &&
    allRc (fun l => Nat.ble 2 l && Nat.blt l (Nat.add 2 C.ns)) x.2.1 &&
    eqLRc (insNRc (mapRc (fun p => wordFR C.L x.2.1 (wordER C.L E x.1 p)) C.Δ)) T

@[expose] noncomputable def topWR (E : List (List Nat)) (ok : Nat → Bool) (ws : List Wit) : Bool :=
  match ws with
  | [x] => Nat.ble 2 x.2.2 && refOK D (Nat.sub x.2.2 2) &&
      Nat.beq (refR D (Nat.sub x.2.2 2)).cls D.mw.length && ok (Nat.sub x.2.2 2) &&
      memWR C E x (refR D (Nat.sub x.2.2 2)).lab
  | [x, y] => Nat.beq x.2.2 0 && Nat.beq y.2.2 1 && memWR C E x (genLabR C [0]) &&
      memWR C E y (genLabR C [1])
  | _ => false

@[expose] noncomputable def gensWR (E : List (List Nat)) (ws : List Wit) (gs : List (List Nat)) :
    Bool :=
  all2 (fun x g => memWR C E x (genLabR C g)) ws gs

@[expose] noncomputable def joinOKR (e : Join) : Bool :=
  Nat.ble e.2.2.1 D.mw.length &&
    bif Nat.blt e.2.2.1 D.mw.length then
      gensWR C (eMem C D e.2.2.1) e.2.2.2.1 (D.mw.getD e.1 []) &&
        gensWR C (eMem C D e.2.2.1) e.2.2.2.2.1 (D.mw.getD e.2.1 []) &&
        gensWR C (eJoin C D e.1 e.2.1) e.2.2.2.2.2 (D.mw.getD e.2.2.1 [])
    else topWR C D (eJoin C D e.1 e.2.1) (fun _ => true) e.2.2.2.2.2

@[expose] noncomputable def globR : Bool :=
  (C.Δ.all fun p => Nat.blt p C.n) && decide (C.Δ.Pairwise (· < ·)) && Nat.ble C.ng C.ns &&
    (List.range C.ns).all (fun i => labF (C.L (Nat.add 2 i)) C.Δ == C.Δ) &&
    (D.sep.all fun p => Nat.blt p C.n) &&
    Nat.beq D.osz.length D.obase.length && Nat.beq D.K.length D.obase.length &&
    Nat.blt 0 D.mw.length && D.mw.getD 0 [[0]] == [] &&
    D.mw.all (fun ws => ws.all fun w => w.all fun l => Nat.blt l 2) &&
    Nat.blt 0 D.Rc.length && Nat.blt 0 D.csz && Nat.beq D.msum.length D.Rc.length &&
    Nat.beq (sumN D.msum) C.N && refOK D D.c0 && (refR D D.c0).w == [] &&
    Nat.ble C.n (Nat.mul D.npc D.pcz) &&
    D.joins.map (fun e => (e.1, e.2.1)) == pairsL D.mw.length && allRc (joinOKR C D) D.joins

end Checks

end CFSG.KC.SLDc

end
