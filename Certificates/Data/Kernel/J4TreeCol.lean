module

public import Certificates.Data.Kernel.J4TreeNode
public import Certificates.Data.Kernel.J4Q.QT

public section

namespace CFSG.KC.J4TreeCol

open CFSG.KC.J4TreeN CFSG.KC.J4Tree CFSG.KC.J4Q CFSG.KC.Loop CFSG.J4Tree.Native

@[expose] def decG : Nat → Nat → List Nat
  | 0, _ => []
  | f + 1, x => if x = 0 then [] else
      (x / 65536 % 256 ^ (x % 65536 - 1)) :: decG f (x / 256 ^ (x % 65536 + 1))

structure CRec where
  k : Nat
  mode : Nat
  kind : Nat
  y : Nat
  om : Nat
  lp : Nat
  cp : Nat
  qp : Nat
  masks : List Nat
  ei : Nat
  rules : List Nat
  seq : Nat
deriving Inhabited

@[expose] def parseCol (l : List Nat) : CRec :=
  match l with
  | k :: mode :: kind :: y :: om :: lp :: cp :: qp :: l =>
    ⟨k, mode, kind, y, om, lp, cp, qp, l.take 15, l.getD 15 0, (l.drop 17).take (l.getD 16 0),
      l.getD (17 + l.getD 16 0) 0⟩
  | _ => default

structure Mats where
  c : Nat
  rm : Nat
  one : Nat
  pad : Nat
  us : List Nat
  ks : List Nat
  g5 : List Nat
  g5i : List Nat

@[expose] def fld (x w m : Nat) : Nat := (x >>> (w * m)) % 2 ^ w

@[expose] def labC (D : CRec) (m : Nat) : Nat := fld D.lp 2 m

@[expose] def pIdx (n i j : Nat) : Nat := i * n - i * (i - 1) / 2 + (j - i)

@[expose] def qC (D : CRec) (n i j : Nat) : Nat :=
  if D.mode = 0 then labC D (i ^^^ j)
  else if i ≤ j then fld D.qp 7 (pIdx n i j) else fld D.qp 7 (pIdx n j i)

@[expose] def sigC (D : CRec) (n i : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun j acc => acc + 2 ^ (10 * (113 * labC D j + qC D n i j))) n

@[expose] def bitsOf (om n : Nat) : List Nat := (List.range n).filter om.testBit

@[expose] def xorSel : List Nat → Nat → Nat
  | [], _ => 0
  | o :: l, mask => (if mask % 2 = 1 then o else 0) ^^^ xorSel l (mask / 2)

@[expose] noncomputable def codesOf (B : List Nat) : List Nat :=
  B.foldl (fun Cs b => Cs ++ Cs.map fun x => M x b) [oneK]

@[expose] noncomputable def labOK (sx : Nat) (D : CRec) (x m : Nat) : Bool :=
  let l := labC D m
  let z := fld D.cp 12 m
  (Nat.beq x oneK == (m == 0)) && ((l == 0) == (m == 0)) &&
    (l == 0 || (l == 1 && is2AK sx x z) || (l == 2 && non2AK sx x z))

@[expose] noncomputable def labsOK (sx : Nat) (D : CRec) (Cs : List Nat) : Bool :=
  (Cs.zipIdx).all fun p => labOK sx D p.1 p.2

@[expose] def uniqOK (D : CRec) (n : Nat) : Bool :=
  let sy := sigC D n D.y
  Nat.blt D.y n && labC D D.y == 1 &&
    (List.range n).all fun i => i == D.y || labC D i != 1 || sigC D n i != sy

@[expose] def unionOK (D : CRec) (n : Nat) (oL : List Nat) : Bool :=
  let so := oL.map fun o => (labC D o, sigC D n o)
  Nat.blt D.om (2 ^ n) && !(D.om.testBit 0) && !(oL.isEmpty) &&
    (List.range n).all fun i => D.om.testBit i ||
      (let li := labC D i
       let si := sigC D n i
       so.all fun p => p.1 != li || p.2 != si)

@[expose] noncomputable def normCodesOK (S Cs : List Nat) (D : CRec) (n : Nat) (oL : List Nat) :
    Bool :=
  D.masks.length == 15 &&
    (S.zip D.masks).all fun p => (oL.zipIdx).all fun q =>
      let o' := xorSel oL (fld p.2 oL.length q.2)
      Nat.blt o' n && Nat.beq (M p.1 (Cs.getD q.1 0)) (M (Cs.getD o' 0) p.1)

@[expose] def p0Codes : List Nat := UK.take 11 ++ KK.take 4

@[expose] noncomputable def kelJ (G : Mats) (e : Nat) : Nat :=
  (pcSeqT e).foldl (fun a i => strictN a fun a' => mulJ G.c G.rm a' (getN G.one G.ks i)) G.one

@[expose] noncomputable def eltJ (G : Mats) (ce : Nat × Nat) : Nat :=
  strictN (etaK G.c G.rm G.one G.us ce.1) fun a => strictN (kelJ G ce.2) fun b => mulJ G.c G.rm a b

@[expose] noncomputable def matsOf (G : Mats) (wv : List (Nat × Nat)) : List Nat :=
  wv.foldl (fun Ms ce => strictL (eltJ G ce) fun b => Ms ++ smapK (fun x => mulJ G.c G.rm x b) Ms)
    [G.one]

@[expose] noncomputable def elimJ (G : Mats) (X t b : Nat) : Nat :=
  Nat.xor X (Nat.land
    (Nat.mul (Nat.land (Nat.land (Nat.div X b) G.c)
      (Nat.xor G.c (Nat.shiftLeft 1 (Nat.mul t 128)))) G.rm)
    (Nat.mul (rowJ G.rm X t) G.c))

@[expose] noncomputable def lowBitJ (v : Nat) : Nat := Nat.land v (Nat.xor v (Nat.sub v 1))

@[expose] noncomputable def gjRank (G : Mats) (X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ rk => rk)
    (fun t ih X rk => strictN (rowJ G.rm X t) fun v =>
      Bool.rec (motive := fun _ => Nat)
        (strictN (elimJ G X t (lowBitJ v)) fun X' => ih X' (Nat.succ rk))
        (ih X rk) (Nat.beq v 0))
    112 X 0

@[expose] noncomputable def pairMat (G : Mats) (Ms : List Nat) (i j : Nat) : Nat :=
  Nat.xor (Nat.xor (Nat.xor (getN 0 Ms (Nat.xor i j)) (getN 0 Ms i)) (getN 0 Ms j)) G.one

@[expose] noncomputable def symJ (G : Mats) (R : List Nat) (nr s : Nat) : Nat :=
  if s ≤ 5 then getN G.one G.g5 (s - 1) else if s ≤ 10 then getN G.one G.g5i (s - 6)
  else getN G.one R (nr - 1 - (s - 11))

@[expose] noncomputable def rulesJ (G : Mats) : List Nat → List Nat → Nat → List Nat
  | [], R, _ => R
  | x :: l, R, nr =>
    strictL (mulJ G.c G.rm (symJ G R nr (x % 65536)) (symJ G R nr (x / 65536))) fun X =>
      rulesJ G l (X :: R) (nr + 1)

@[expose] noncomputable def seqJ (G : Mats) (R : List Nat) (nr : Nat) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | f + 1, sq, acc => if sq % 65536 = 0 then acc else
      strictN (mulJ G.c G.rm acc (symJ G R nr (sq % 65536))) fun a => seqJ G R nr f (sq / 65536) a

@[expose] noncomputable def normMatsOK (G : Mats) (P Ms : List Nat) (D : CRec) (n : Nat)
    (oL : List Nat) (E : Nat) : Bool :=
  D.masks.length == 15 && canonJ G.pad D.ei && Nat.beq (mulJ G.c G.rm E D.ei) G.one &&
    (P.zip D.masks).all fun p =>
      (strictB (mulJ G.c G.rm (mulJ G.c G.rm E p.1) D.ei) fun X =>
        (oL.zipIdx).all fun q =>
          let o' := xorSel oL (fld p.2 oL.length q.2)
          Nat.blt o' n &&
            Nat.beq (mulJ G.c G.rm X (getN 0 Ms q.1)) (mulJ G.c G.rm (getN 0 Ms o') X))

@[expose] noncomputable def colNodeOK (G : Mats) (T : Tabs) (D : CRec) : Bool :=
  let wv := treeWv D.k
  let B := wv.map (ccT T)
  let n := 2 ^ wv.length
  let Cs := codesOf B
  let oL := bitsOf D.om n
  Nat.ble wv.length 9 && wv.all coordOK && B.all (fun b => sqOneK b && B.all fun b' => commK b b') &&
    Nat.ble D.mode 1 && labsOK T.sx D Cs &&
    if D.kind = 0 then uniqOK D n
    else unionOK D n oL &&
      if D.kind = 1 then normCodesOK p0Codes Cs D n oL
      else D.kind == 2 &&
        (let R := rulesJ G D.rules [] 0
         normMatsOK G (G.us ++ G.ks) (matsOf G wv) D n oL (seqJ G R D.rules.length 4096 D.seq G.one))

@[expose] noncomputable def pairsOK (G : Mats) (D : CRec) (t0 cnt : Nat) : Bool :=
  let wv := treeWv D.k
  let n := 2 ^ wv.length
  let Ms := matsOf G wv
  D.mode == 1 && (List.range n).all fun i => (List.range (n - i)).all fun d =>
    let t := pIdx n i (i + d)
    !(Nat.ble t0 t && Nat.blt t (t0 + cnt)) ||
      Nat.beq (fld D.qp 7 t + gjRank G (pairMat G Ms i (i + d))) 112

end CFSG.KC.J4TreeCol

end
