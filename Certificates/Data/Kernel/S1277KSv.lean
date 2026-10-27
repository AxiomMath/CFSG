module

public import Certificates.Data.Kernel.S1277KSig
public import Certificates.Data.Kernel.S1277KCand

public section

namespace CFSG.KC.S1277Sv

open CFSG.KC.S1277Lat CFSG.KC.S1277Mod CFSG.KC.S1277Sig CFSG.KC.S1277Cand CFSG.KC.S1277Gm
  CFSG.KC.Enum

@[expose] def oneQ : ℕ := 1 + 64 * (2 + 64 * (4 + 64 * (8 + 64 * (16 + 64 * 32))))

@[expose] def mulQ (x y : ℕ) : ℕ :=
  appP x (y % 64) + 64 * (appP x ((y >>> 6) % 64) + 64 * (appP x ((y >>> 12) % 64) +
    64 * (appP x ((y >>> 18) % 64) + 64 * (appP x ((y >>> 24) % 64) +
      64 * appP x ((y >>> 30) % 64)))))

@[expose] def colsQ (g : ℕ) : List ℕ :=
  [g % 64, (g >>> 6) % 64, (g >>> 12) % 64, (g >>> 18) % 64, (g >>> 24) % 64, (g >>> 30) % 64]

@[expose] def packQ (f : ℕ → ℕ) : ℕ :=
  f 0 + 64 * (f 1 + 64 * (f 2 + 64 * (f 3 + 64 * (f 4 + 64 * f 5))))

@[expose] def rd36 (P n : ℕ) : ℕ := (P >>> (36 * n)) % 68719476736

@[expose] def rd2 (v k : ℕ) : ℕ := (v >>> (2 * k)) % 4

@[expose] noncomputable def wordQ (gl w : List ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun x => x)
    (fun j _ ih x => strictN (mulQ x (gl.getD j 0)) ih) w oneQ

@[expose] noncomputable def incL (b : ℕ) (l : List ℕ) : Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun a _ ih p => Nat.blt p a && ih a) l b

@[expose] noncomputable def treeQ (el par lt dp gl : List ℕ) : Bool :=
  allL (List.range el.length) fun i =>
    Nat.beq (el.getD i 0) oneQ ||
      (Nat.blt (par.getD i 0) el.length && Nat.blt (lt.getD i 0) gl.length &&
        Nat.blt (dp.getD (par.getD i 0) 0) (dp.getD i 0) &&
        Nat.beq (mulQ (el.getD (par.getD i 0) 0) (gl.getD (lt.getD i 0) 0)) (el.getD i 0))

@[expose] noncomputable def sgChk (M : Mdl) (kg : List ℕ) (TP : ℕ) (ws sg : List ℕ) : Bool :=
  Nat.beq sg.length kg.length &&
    allL (List.range kg.length) fun j =>
      Nat.beq (sg.getD j 0) (packQ fun i => rd6 TP (M.conj (kg.getD j 0) (ws.getD (2 ^ i) 0)))

@[expose] noncomputable def sChk (M : Mdl) (kg : List ℕ) (TP : ℕ) (ws sg sl sp sj sd : List ℕ) :
    Bool :=
  sgChk M kg TP ws sg && Nat.beq sl.length 24 && incL 0 sl && treeQ sl sp sj sd sg

@[expose] noncomputable def pChk (sl pl pi : List ℕ) : Bool :=
  Nat.beq pl.length 8 && incL 0 pl && memL oneQ pl &&
    allL pl (fun a => allL pl fun b => memL (mulQ a b) pl) &&
    allL (List.range 8) (fun i => Nat.beq (mulQ (pl.getD i 0) (pl.getD (pi.getD i 0) 0)) oneQ) &&
    allL pl (fun p => memL p sl)

@[expose] noncomputable def sigQ (L : ℕ) (b : List ℕ) (g : ℕ) : Bool :=
  Nat.blt g 68719476736 && tChk 6 L b 0 (colsQ g)

@[expose] noncomputable def vgChk (L : ℕ) (b vg : List ℕ) : Bool :=
  Nat.beq vg.length 130 && allL vg (sigQ L b)

@[expose] noncomputable def hpChk (vg sl : List ℕ) (sp36 hp : ℕ) : Bool :=
  allLt 24 (fun t => Nat.beq (rd36 sp36 t) (sl.getD t 0)) &&
    allLt 130 fun k => strictB (vg.getD k 0) fun g =>
      allLt 24 fun t => Nat.beq (rd36 hp (k * 24 + t)) (mulQ g (rd36 sp36 t))

@[expose] def tyL (ty : ℕ) (sl a1 a2 : List ℕ) : List ℕ :=
  bif Nat.beq ty 0 then sl else bif Nat.beq ty 2 then a1 else a2

@[expose] noncomputable def covR (sp36 hp vt : ℕ) (sl a1 a2 : List ℕ) (r p : ℕ) : ℕ :=
  strictN (mulQ (rd36 sp36 (r % 24)) (rd36 hp (r / 24))) fun y =>
    bif Nat.blt r 74880 && Nat.blt p y &&
        (Nat.beq (rd2 vt (r / 576)) 1 || memL y (tyL (rd2 vt (r / 576)) sl a1 a2))
      then y else 68719476736

@[expose] noncomputable def covL (sp36 hp vt : ℕ) (sl a1 a2 : List ℕ) (rs : List ℕ) (p : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun p => p)
    (fun r _ ih p => strictN (covR sp36 hp vt sl a1 a2 r p) ih) rs p

@[expose] noncomputable def covChk (sp36 hp vt : ℕ) (sl a1 a2 : List ℕ) (vr : List (List ℕ))
    (vb : List ℕ) (c : ℕ) : Bool :=
  Nat.blt (vb.getD (c + 1) 0) 68719476736 &&
    Nat.beq (covL sp36 hp vt sl a1 a2 (vr.getD c []) (vb.getD c 0)) (vb.getD (c + 1) 0)

@[expose] noncomputable def cntChk (vr : List (List ℕ)) (vb : List ℕ) : Bool :=
  Nat.beq ((List.range vr.length).map fun c => (vr.getD c []).length).sum 40320 &&
    Nat.beq (vb.getD 0 0) 0

@[expose] noncomputable def witY (pl : List ℕ) (x : ℕ) (px : List ℕ) : Bool :=
  !memL x pl && memL (mulQ x x) pl && allL pl fun p => memL (mulQ x p) px

@[expose] noncomputable def witX (pl : List ℕ) (x : ℕ) : Bool :=
  witY pl x (pl.map fun q => mulQ q x)

@[expose] noncomputable def witQ (pl gl w : List ℕ) : Bool :=
  allL w (fun j => Nat.blt j gl.length) && strictB (wordQ gl w) (witX pl)

@[expose] noncomputable def wSChk (pl sg vg : List ℕ) (vt : ℕ) (vw : List (List ℕ)) (k : ℕ) :
    Bool :=
  !Nat.beq (rd2 vt k) 1 || witQ pl (sg ++ [vg.getD k 0]) (vw.getD k [])

@[expose] noncomputable def wAChk (pl sg vg : List ℕ) (vt ki ty : ℕ) (w : List (List ℕ)) (k : ℕ) :
    Bool :=
  Nat.beq (rd2 vt k) 0 || Nat.beq (rd2 vt k) ty ||
    witQ pl (sg ++ [vg.getD ki 0, vg.getD k 0]) (w.getD k [])

@[expose] noncomputable def aChk1 (sg sl vg : List ℕ) (vt ki ty : ℕ) (a ap aj ad : List ℕ) : Bool :=
  Nat.blt ki 130 && Nat.beq (rd2 vt ki) ty &&
    allLt 130 (fun k => !Nat.beq (rd2 vt k) ty || Nat.beq k ki) &&
    Nat.beq a.length 168 && incL 0 a && treeQ a ap aj ad (sg ++ [vg.getD ki 0]) &&
    allL sl (fun s => memL s a)

end CFSG.KC.S1277Sv

end
