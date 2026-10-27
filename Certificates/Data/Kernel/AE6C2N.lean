module

public import Certificates.Data.Kernel.AE6FN
public import Certificates.Data.Kernel.KGC31PB
public import Certificates.Data.AE6CertC2

public section

namespace CFSG.KC.AE6C2

open CFSG.KC.Enum CFSG.KS CFSG.KC.YoshQ CFSG.KC.AE6F CFSG.KC.KGC31P Certificates.AE6Model
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6 (curtisRels curtisRankOne)

@[expose] noncomputable def qsN (PL : List Nat) (g gi : Nat) : List Nat :=
  PL.filter fun x => memN PL (conjN g gi x)

@[expose] noncomputable def qsAllN (PL G : List Nat) : List (List Nat) :=
  (List.range 8).map fun i => qsN PL (G.getD i (pidn 360 9)) (invN 360 9 (G.getD i (pidn 360 9)))

@[expose] noncomputable def commAllN (Q : List Nat) (X : Nat) : Bool :=
  Q.all fun q => Nat.beq (pc 360 9 X q) (pc 360 9 q X)

@[expose] noncomputable def pt (x i : Nat) : Nat := pg 9 (mask 9) x i

@[expose] noncomputable def prPt (F : List Nat) (h q u v : Nat) : Bool :=
  !(F.any (Nat.beq v)) || Nat.beq (pt h v) (pt q (pt h u))

@[expose] noncomputable def prOK (Q F : List Nat) (h : Nat) : Bool :=
  Q.all fun q => F.all fun u => prPt F h q u (pt q u)

@[expose] noncomputable def prStep (pr : Nat → Bool) (k : Nat → List Nat) (acc : List Nat)
    (h : Nat) : List Nat :=
  Bool.rec acc (k h) (pr h)

@[expose] noncomputable def pfilterPr (fk : Nat → Bool) :
    List (List Nat × (Nat → Bool)) → Nat → List Nat → List Nat
  | [], g, acc => if fk g then g :: acc else acc
  | (T, pr) :: Ts, g, acc =>
    T.foldl (fun acc t => prStep pr (fun h => pfilterPr fk Ts h acc) acc (pc 360 9 g t)) acc

@[expose] noncomputable def prLv (Q : List Nat) :
    List Nat → List (List Nat) → List Nat → List (List Nat × (Nat → Bool))
  | F, L :: Ls, b :: B => (L, prOK Q (b :: F)) :: prLv Q (b :: F) Ls B
  | _, _, _ => []

@[expose] noncomputable def fixLv : List Nat → List (List Nat) → List Nat → Bool
  | F, L :: Ls, b :: B =>
    (L.all fun t => F.all fun u => Nat.beq (pt t u) u) && fixLv (b :: F) Ls B
  | _, [], _ => true
  | _, _ :: _, [] => false

@[expose] noncomputable def l3N (Q B : List Nat) (Ls : List (List Nat)) : List Nat :=
  pfilterPr (commAllN Q) (prLv Q [] Ls B) (pidn 360 9) []

@[expose] noncomputable def lsN (Qs : List (List Nat)) (L3 : List Nat) : List (List Nat) :=
  Qs.map fun Q => L3.filter (commAllN Q)

@[expose] noncomputable def c2BasicN (G PL : List Nat) (Qs Ls : List (List Nat)) : Bool :=
  let Z := awN G zWord
  let Q3 := Qs.getD 3 []
  pWordsC2.all (fun w => memN PL (awN G w)) && Qs.length == 8 &&
    Qs.all (fun Q => memN Q Z && Q3.all (memN Q)) &&
    Ls.all fun L => L.all fun T => eqN 360 9 (pmN 360 9 (invN 360 9 T) T) (pidn 360 9)

@[expose] noncomputable def c2HTN (GT : List (Nat × Nat)) (cs : List Nat) : List (Nat × Nat) :=
  (List.range 8).map fun i =>
    let gp := GT.getD i (pidn 360 9, pidn 360 9)
    let T := cs.getD i (pidn 360 9)
    (pmN 360 9 gp.1 T, pmN 360 9 (invN 360 9 T) gp.2)

@[expose] noncomputable def wordHN (HT : List (Nat × Nat)) (w : List Nat) : Nat :=
  w.foldl (fun acc i => pmN 360 9 acc (HT.getD i (pidn 360 9, pidn 360 9)).1) (pidn 360 9)

@[expose] noncomputable def wordsN (GT : List (Nat × Nat)) (TG : List (List Nat × Nat))
    (cs : List Nat) : Bool :=
  TG.all fun wt => eqN 360 9 (wordHN (c2HTN GT cs) wt.1) wt.2

@[expose] noncomputable def relsN (GT : List (Nat × Nat)) (R : List (List Nat)) (cs : List Nat) :
    Bool :=
  R.all fun r => eqN 360 9 (evalHN (c2HTN GT cs) r) (pidn 360 9)

@[expose] noncomputable def idZN (ZC cs : List Nat) : Bool :=
  (List.range 8).all (fun i => eqN 360 9 (cs.getD i (pidn 360 9)) (pidn 360 9)) ||
    (List.range 8).all fun i => eqN 360 9 (cs.getD i (pidn 360 9)) (ZC.getD i (pidn 360 9))

@[expose] noncomputable def c2PN (GT : List (Nat × Nat)) (TG : List (List Nat × Nat))
    (ZC cs : List Nat) : Bool :=
  !(wordsN GT TG cs && relsN GT curtisRels cs) || idZN ZC cs

@[expose] noncomputable def treeN (GT : List (Nat × Nat)) (TG : List (List Nat × Nat))
    (ZC : List Nat) (Ls : List (List Nat)) : Bool :=
  (Ls.getD 0 []).all fun c0 => (Ls.getD 2 []).all fun c2 => (Ls.getD 4 []).all fun c4 =>
    (Ls.getD 6 []).all fun c6 =>
    !(wordsN GT TG [c0, pidn 360 9, c2, pidn 360 9, c4, pidn 360 9, c6, pidn 360 9]) ||
    (Ls.getD 1 []).all fun c1 =>
    (!(relsN GT (curtisRankOne 0) [c0, c1, pidn 360 9, pidn 360 9, pidn 360 9, pidn 360 9,
        pidn 360 9, pidn 360 9]) ||
    (Ls.getD 3 []).all fun c3 =>
    (!(relsN GT (curtisRankOne 1) [pidn 360 9, pidn 360 9, c2, c3, pidn 360 9, pidn 360 9,
        pidn 360 9, pidn 360 9]) ||
    (Ls.getD 5 []).all fun c5 =>
    (!(relsN GT (curtisRankOne 2) [pidn 360 9, pidn 360 9, pidn 360 9, pidn 360 9, c4, c5,
        pidn 360 9, pidn 360 9]) ||
    (Ls.getD 7 []).all fun c7 =>
    (!(relsN GT (curtisRankOne 3) [pidn 360 9, pidn 360 9, pidn 360 9, pidn 360 9,
        pidn 360 9, pidn 360 9, c6, c7]) ||
      (!(relsN GT curtisRels [c0, c1, c2, c3, c4, c5, c6, c7]) ||
        idZN ZC [c0, c1, c2, c3, c4, c5, c6, c7])))))

end CFSG.KC.AE6C2

end
