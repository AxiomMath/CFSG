module

public import Certificates.Data.Kernel.J4TreeCode
public import Certificates.Data.CFSGNative.J4Tree.Index

public section

universe u

namespace CFSG.KC.J4TreeN

open CFSG.KC.J4Tree CFSG.KC.F2W CFSG.J4Tree.Native

@[expose] noncomputable def M (a b : Nat) : Nat := mulW 12 a b

@[expose] def UK : List Nat := tblC uCode
@[expose] def KK : List Nat := tblC kCode
@[expose] def XK : List Nat := tblC xCode
@[expose] def XiK : List Nat := tblC xiCode

@[expose] noncomputable def kelCK (e : Nat) : Nat :=
  (pcSeqT e).foldl (fun acc i => M acc (KK.getD i oneK)) oneK

@[expose] def ltr (d : Nat) : Int :=
  if d = 1 then 1 else if d = 2 then 2 else if d = 3 then 3 else if d = 4 then -1
  else if d = 5 then -2 else -3

@[expose] def digitsL : Nat → Nat → List Int
  | 0, _ => []
  | f + 1, v => if v % 8 = 0 then [] else ltr (v % 8) :: digitsL f (v / 8)

@[expose] def wordC : Nat → Nat → List Int
  | 0, _ => []
  | f + 1, w => if w = 0 then [] else digitsL 4 (w % 4096) ++ wordC f (w / 4096)

structure Tabs where
  eta : Nat → Nat
  kel : Nat → Nat
  w4 : Nat → Nat
  sx : Nat

@[expose] noncomputable def tabsOK (T : Tabs) : Bool :=
  (List.range 2048).all (fun c => Nat.beq (T.eta c) (etaCK UK c)) &&
    (List.range 1024).all (fun e => Nat.beq (T.kel e) (kelCK e)) &&
    (List.range 4096).all (fun v => Nat.beq (T.w4 v) (wordCK XK XiK (digitsL 4 v)))

@[expose] noncomputable def sxOf (zm : List Nat) : Nat :=
  zm.foldl (fun acc c => acc ||| 2 ^ ((etaCK UK c) % 2 ^ 12 / 2)) 0

@[expose] noncomputable def ccT (T : Tabs) (ce : Nat × Nat) : Nat := M (T.eta ce.1) (T.kel ce.2)

@[expose] noncomputable def wordT (T : Tabs) : Nat → Nat → Nat
  | 0, _ => oneK
  | f + 1, w => if w = 0 then oneK else M (T.w4 (w % 4096)) (wordT T f (w / 4096))

@[expose] def coordOK (ce : Nat × Nat) : Bool := Nat.blt ce.1 2048 && Nat.blt ce.2 1024

@[expose] noncomputable def prodFrom : Nat → List Nat → Nat → Nat
  | acc, [], _ => acc
  | acc, x :: L, m => prodFrom (if m % 2 = 1 then M acc x else acc) L (m / 2)

@[expose] noncomputable def prodMask (L : List Nat) (m : Nat) : Nat := prodFrom oneK L m

@[expose] noncomputable def commK (a b : Nat) : Bool := Nat.beq (M a b) (M b a)

@[expose] noncomputable def sqOneK (a : Nat) : Bool := Nat.beq (M a a) oneK

@[expose] noncomputable def invK (a b : Nat) : Bool := Nat.beq (M a b) oneK && Nat.blt b (2 ^ 144)

@[expose] def inEK (a : Nat) : Bool :=
  (List.range 11).all fun i => a / 2 ^ (12 * (i + 1)) % 2 ^ 12 == 2 ^ (i + 1)

@[expose] def translK (a : Nat) : Nat := a % 2 ^ 12 / 2

@[expose] def spreadZ (z : Nat) : Nat :=
  (List.range 12).foldl (fun acc k => if z.testBit k then acc ||| 2 ^ (12 * k) else acc) 0 * 4095

@[expose] noncomputable def colK (a z : Nat) : Nat :=
  (List.range 12).foldl
    (fun acc i => if (M a (spreadZ z)).testBit (12 * i) then acc ||| 2 ^ i else acc) 0

@[expose] noncomputable def sepK (a z : Nat) : Bool := Nat.beq (colK a z ^^^ z) 1

@[expose] def fixK (a v : Nat) : Bool :=
  v % 2 == 1 && decide (v < 4096) &&
    ((List.range 12).foldl (fun acc i => if v.testBit i then acc ^^^ (a / 2 ^ (12 * i) % 2 ^ 12)
      else acc) 0 == v)

@[expose] noncomputable def non2AK (sx a z : Nat) : Bool :=
  if inEK a then !(sx.testBit (translK a)) else sepK a z

@[expose] def is2AK (sx a v : Nat) : Bool := if inEK a then sx.testBit (translK a) else fixK a v

@[expose] def QK : Nat := packL [1, 2, 6, 12, 32, 16, 290, 150, 1310, 950, 78, 3640]
@[expose] def QiK : Nat := packL [1, 2, 6, 14, 32, 16, 1034, 164, 82, 706, 376, 2948]

@[expose] def posL : List (Nat × Nat) :=
  (List.range 11).flatMap fun d => (List.range (11 - d)).map fun i => (i, i + d + 1)

@[expose] def utK (y : Nat) : Bool :=
  (List.range 12).all fun i => y / 2 ^ (12 * i) % 2 ^ (i + 1) == 2 ^ i

@[expose] def leadOf (y : Nat) : Nat :=
  ((posL.zipIdx).find? fun p => y.testBit (12 * p.1.1 + p.1.2)).elim 66 Prod.snd

@[expose] noncomputable def qconj (a : Nat) : Nat := M (M QK a) QiK

@[expose] def incrFrom : Nat → List Nat → Bool
  | _, [] => true
  | lo, x :: l => Nat.ble lo x && incrFrom (x + 1) l

@[expose] noncomputable def leadsOK (L : List Nat) : Bool :=
  L.all (fun a => utK (qconj a)) &&
    (let ls := L.map fun a => leadOf (qconj a)
     incrFrom 0 ls && ls.all fun p => Nat.blt p 66)

structure KRec where
  u : Nat
  tgt : Nat
  h : Nat
  hI : Nat
  msk : List Nat
  root : Nat
  orb : List (Nat × Nat × Nat × Nat)
  tC : List (Nat × Nat)
  bC : List (Nat × Nat)
  eflag : Nat
deriving Inhabited

structure NRec where
  n : Nat
  r : Nat
  sC : List (Nat × Nat)
  sI : List Nat
  aM : Nat
  beta : List Nat
  gamma : List Nat
  nW : List Nat
  nI : List Nat
  nD : List (List Nat)
  ents : List (Nat × Nat × Nat × Nat × Nat)
  nonF : List (Nat × List Nat)
  kids : List KRec
deriving Inhabited

@[expose] def decF : Nat → Nat → List Nat
  | 0, _ => []
  | f + 1, x => if x = 0 then [] else
      (x / 256 % 256 ^ (x % 256 - 1)) :: decF f (x / 256 ^ (x % 256))

@[expose] def pairs : List Nat → List (Nat × Nat)
  | a :: b :: l => (a, b) :: pairs l
  | _ => []

@[expose] def groups (k : Nat) : Nat → List Nat → List (List Nat)
  | 0, _ => []
  | f + 1, l => if l.isEmpty then [] else l.take k :: groups k f (l.drop k)

@[expose] def quints : List Nat → List (Nat × Nat × Nat × Nat × Nat)
  | a :: b :: c :: d :: e :: l => (a, b, c, d, e) :: quints l
  | _ => []

@[expose] def quads : List Nat → List (Nat × Nat × Nat × Nat)
  | a :: b :: c :: d :: l => (a, b, c, d) :: quads l
  | _ => []

@[expose] def parseKids (r : Nat) : Nat → List Nat → List KRec
  | 0, _ => []
  | f + 1, l =>
    match l with
    | u :: tgt :: h :: hI :: nm :: l =>
      let msk := l.take nm
      let l := l.drop nm
      match l with
      | root :: no :: l =>
        let orb := quads (l.take (4 * no))
        let l := l.drop (4 * no)
        match l with
        | nt :: l =>
          let tC := pairs (l.take (2 * nt))
          let l := l.drop (2 * nt)
          match l with
          | nb :: l =>
            let bC := pairs (l.take (2 * nb))
            let l := l.drop (2 * nb)
            match l with
            | ef :: l => ⟨u, tgt, h, hI, msk, root, orb, tC, bC, ef⟩ :: parseKids r f l
            | [] => []
          | [] => []
        | [] => []
      | _ => []
    | _ => []

@[expose] def parseRec (l : List Nat) : NRec :=
  match l with
  | n :: r :: nw :: ne :: nn :: nk :: l =>
    let sC := pairs (l.take (2 * n))
    let l := l.drop (2 * n)
    let sI := l.take n
    let l := l.drop n
    match l with
    | aM :: l =>
      let beta := l.take r
      let l := l.drop r
      let gamma := l.take r
      let l := l.drop r
      let nW := l.take nw
      let l := l.drop nw
      let nI := l.take nw
      let l := l.drop nw
      let nD := groups r nw (l.take (nw * r))
      let l := l.drop (nw * r)
      let ents := quints (l.take (5 * ne))
      let l := l.drop (5 * ne)
      let nonF := (groups (1 + 2 ^ r) nn (l.take (nn * (1 + 2 ^ r)))).map
        fun g => (g.headD 0, g.drop 1)
      let l := l.drop (nn * (1 + 2 ^ r))
      ⟨n, r, sC, sI, aM, beta, gamma, nW, nI, nD, ents, nonF, parseKids r nk l⟩
    | [] => default
  | _ => default

@[expose] def filt {α : Type u} : List Bool → List α → Bool → List α
  | f :: fs, x :: xs, b => if f = b then x :: filt fs xs b else filt fs xs b
  | _, _, _ => []

@[expose] def flagsOf (n aM : Nat) : List Bool := (List.range n).map aM.testBit

@[expose] noncomputable def enumOK (f : Nat → Nat → Bool) : List Nat → Nat → Nat → Nat → Bool
  | [], X, u, _ => f X u
  | s :: l, X, u, t => enumOK f l X u (t + 1) && enumOK f l (M X s) (u + 2 ^ t) (t + 1)

@[expose] noncomputable def cosetOK (S : List Nat) (L X u : Nat) : Bool :=
  !(sqOneK X && u != 0) || (L.testBit u && S.any fun s => !commK s X)

@[expose] noncomputable def cosetsOK (S : List Nat) (L : Nat) (l : List Nat) : Bool :=
  enumOK (cosetOK S L) l oneK 0 0

@[expose] def coverBits (ents : List (Nat × Nat × Nat × Nat × Nat)) (nonF : List (Nat × List Nat)) :
    Nat :=
  (nonF.map Prod.fst).foldl (fun acc u => acc ||| 2 ^ u) (ents.foldl (fun acc e => acc ||| 2 ^ e.1) 0)

@[expose] noncomputable def entsOK (NA AI N NI : List Nat) (kidU : List Nat) :
    List Nat → Nat → List (Nat × Nat × Nat × Nat × Nat) → Bool
  | _, _, [] => true
  | Rs, i, (u, kid, par, lab, v) :: es =>
    let R := prodMask NA u
    (if kid != 0 then kidU.getD (kid - 1) 0 == u && Nat.blt (kid - 1) kidU.length
     else Nat.blt par i && Nat.blt lab N.length &&
       Nat.beq (M (M (N.getD lab 0) (Rs.getD (i - 1 - par) 0)) (NI.getD lab 0))
         (M R (prodMask AI v))) &&
      entsOK NA AI N NI kidU (R :: Rs) (i + 1) es

@[expose] noncomputable def nonFOK (sx : Nat) (NA AI : List Nat) (c : Nat × List Nat) : Bool :=
  let R := prodMask NA c.1
  (List.range (2 ^ AI.length)).all fun v => non2AK sx (M R (prodMask AI v)) (c.2.getD v 0)

@[expose] noncomputable def normOK (B : List Nat) (N NI : List Nat) (nD : List (List Nat)) : Bool :=
  (List.range N.length).all fun l => invK (N.getD l 0) (NI.getD l 0) &&
    (List.range B.length).all fun j =>
      Nat.beq (M (M (N.getD l 0) (B.getD j 0)) (NI.getD l 0)) (prodMask B ((nD.getD l []).getD j 0))

@[expose] noncomputable def orbOK (S SI : List Nat) (Y root : Nat)
    (orb : List (Nat × Nat × Nat × Nat)) : Bool :=
  Nat.blt root orb.length && incrFrom 0 (orb.map Prod.fst) &&
    (orb.map Prod.fst).all (fun x => Nat.blt x (2 ^ 144)) &&
    (orb.zipIdx).all fun p =>
      if p.2 = root then Nat.beq p.1.1 Y && p.1.2.2.2 == 0
      else
        let q := orb.getD p.1.2.1 (0, 0, 0, 0)
        Nat.blt p.1.2.1 orb.length && Nat.blt p.1.2.2.1 S.length &&
          p.1.2.2.2 == q.2.2.2 + 1 &&
          Nat.beq p.1.1 (M (M (S.getD p.1.2.2.1 0) q.1) (SI.getD p.1.2.2.1 0))

@[expose] noncomputable def mergeOK (T : Tabs) (B : List Nat) (n Y : Nat) (kd : KRec) : Bool :=
  let H := wordT T 64 kd.h
  let TB := (treeBasis kd.tgt).map (ccT T)
  !(treeTopIds.contains kd.tgt) && Nat.ble 1 kd.tgt && Nat.ble kd.tgt treeN &&
    (treeBasis kd.tgt).all coordOK && invK H kd.hI &&
    (List.range (B.length + 1)).all (fun j =>
      Nat.beq (M (M kd.hI ((B ++ [Y]).getD j 0)) H) (prodMask TB (kd.msk.getD j 0))) &&
    kd.orb.length * treeOrd kd.tgt == 2 ^ n

@[expose] noncomputable def prunedOK (T : Tabs) (B : List Nat) (n Y : Nat) (kd : KRec) : Bool :=
  let Tc := kd.tC.map (ccT T)
  let Z := kd.bC.map (ccT T)
  kd.tC.all coordOK && kd.bC.all coordOK &&
    (Tc ++ Z).all (fun t => (Y :: B).all fun b => commK t b) && leadsOK Tc && leadsOK Z &&
    Z.all (fun z => sqOneK z && (Tc ++ Z).all fun t => commK z t) &&
    kd.orb.length * 2 ^ kd.tC.length == 2 ^ n &&
    (if kd.eflag = 1 then Z.all inEK && Nat.ble 7 Z.length else Nat.ble 11 Z.length)

@[expose] noncomputable def kidOK (T : Tabs) (B S SI NA : List Nat) (n : Nat) (kd : KRec) : Bool :=
  let Y := prodMask NA kd.u
  Nat.blt kd.u (2 ^ NA.length) && orbOK S SI Y kd.root kd.orb &&
    if kd.tgt = 0 then prunedOK T B n Y kd else mergeOK T B n Y kd

@[expose] noncomputable def nodeChkWith (T : Tabs) (k : Nat) (D : NRec) (B S : List Nat) : Bool :=
  let NA := filt (flagsOf D.n D.aM) S false
  let AI := filt (flagsOf D.n D.aM) S true
  let N := D.nW.map (wordT T 64)
  Nat.beq (M QK QiK) oneK && (treeBasis k).all coordOK && D.sC.all coordOK &&
    treeOrd k == 2 ^ D.n && D.sC.length == D.n && D.sI.length == D.n &&
    D.r == (treeBasis k).length && Nat.blt D.aM (2 ^ D.n) &&
    B.all (fun b => sqOneK b && B.all fun b' => commK b b') &&
    (S.zip D.sI).all (fun p => invK p.1 p.2) && S.all (fun s => B.all fun b => commK s b) &&
    leadsOK S &&
    D.beta.length == AI.length && (AI.zip D.beta).all (fun p => Nat.beq p.1 (prodMask B p.2)) &&
    D.gamma.length == B.length &&
    (B.zip D.gamma).all (fun p => Nat.blt p.2 (2 ^ AI.length) && Nat.beq p.1 (prodMask AI p.2)) &&
    normOK B N D.nI D.nD &&
    entsOK NA AI N D.nI (D.kids.map KRec.u) [] 0 D.ents &&
    D.nonF.all (nonFOK T.sx NA AI) &&
    D.kids.all (kidOK T B S D.sI NA D.n) &&
    cosetsOK S (coverBits D.ents D.nonF) NA

@[expose] noncomputable def enumZ (f : Nat → Nat → Nat → Bool) :
    List Nat → Nat → Nat → Nat → List Nat → Bool
  | [], X, u, _, zs => f X u (zs.headD 0)
  | s :: l, X, u, t, zs => enumZ f l X u (t + 1) (zs.take (2 ^ l.length)) &&
      enumZ f l (M X s) (u + 2 ^ t) (t + 1) (zs.drop (2 ^ l.length))

structure WRec where
  wmask : List Nat
  comp : List Nat
  bmask : List Nat
  wcert : List Nat
  certs : List Nat
deriving Inhabited

@[expose] def parseW (r : Nat) (l : List Nat) : WRec :=
  match l with
  | nw :: nc :: l =>
    ⟨l.take nw, (l.drop nw).take nc, (l.drop (nw + nc)).take r, (l.drop (nw + nc + r)).take nw,
      l.drop (2 * nw + nc + r)⟩
  | _ => default

@[expose] noncomputable def wChk (T : Tabs) (k : Nat) (D : WRec) : Bool :=
  let B := (treeBasis k).map (ccT T)
  let Wc := (treeWv k).map (ccT T)
  let G := Wc ++ D.comp.map (prodMask B)
  (treeBasis k).all coordOK && (treeWv k).all coordOK &&
    D.wmask.length == Wc.length && D.wcert.length == Wc.length && G.length == B.length &&
    D.bmask.length == B.length && D.certs.length == 2 ^ G.length &&
    B.all (fun b => sqOneK b && B.all fun b' => commK b b') &&
    (Wc.zip D.wmask).all (fun p => Nat.beq p.1 (prodMask B p.2)) &&
    (B.zip D.bmask).all (fun p => Nat.blt p.2 (2 ^ G.length) && Nat.beq p.1 (prodMask G p.2)) &&
    (Wc.zip D.wcert).all (fun p => !(Nat.beq p.1 oneK) && is2AK T.sx p.1 p.2) &&
    enumZ (fun X m z => Nat.blt m (2 ^ Wc.length) || Nat.beq X oneK || non2AK T.sx X z) G oneK 0 0
      D.certs

@[expose] noncomputable def nodeChk (T : Tabs) (k : Nat) (D : NRec) : Bool :=
  nodeChkWith T k D ((treeBasis k).map (ccT T)) (D.sC.map (ccT T))

end CFSG.KC.J4TreeN

end
