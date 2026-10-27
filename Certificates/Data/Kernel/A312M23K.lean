module

public import Certificates.Data.Kernel.A312HeK

public section

namespace CFSG.KC.A312M23K

open CFSG.KC.E64F CFSG.KC.A312HeK

@[expose] noncomputable def tf (T : List (List Nat)) (l p : Nat) : Nat := (T.getD l []).getD p 0

@[expose] noncomputable def eqP (T : List (List Nat)) (n : Nat) (u v : List Nat) : Bool :=
  (List.range n).all fun p => Nat.beq (wordF (tf T) u p) (wordF (tf T) v p)

@[expose] noncomputable def idP (T : List (List Nat)) (n : Nat) (u : List Nat) : Bool :=
  (List.range n).all fun p => Nat.beq (wordF (tf T) u p) p

@[expose] noncomputable def sh (k : Nat) (w : List Nat) : List Nat := w.map fun l => k + l

@[expose] noncomputable def letChk (T AB S gw : List (List Nat)) (n : Nat) : Bool :=
  (List.range S.length).all (fun i => (List.range n).all fun p => Nat.beq (tf T i p) (tf S i p)) &&
    gw.all (bnd AB.length) &&
    (List.range gw.length).all fun g => (List.range n).all fun p =>
      Nat.beq (tf T (S.length + g) p) (wordF (tf AB) (gw.getD g []) p)

@[expose] noncomputable def alphChk (T : List (List Nat)) (n nL : Nat)
    (xs : List (List Nat × Nat × Nat)) (t : List Nat × Nat × Nat) (ws : List (List Nat)) : Bool :=
  (List.range xs.length).all (fun i =>
      bnd nL (xs.getD i ([], 0, 0)).1 &&
        eqP T n [nL + i] (repW (xs.getD i ([], 0, 0)).2.1 (xs.getD i ([], 0, 0)).1) &&
        idP T n [nL + xs.length + i, nL + i] && Nat.beq ((xs.getD i ([], 0, 0)).2.2 % 2) 1 &&
        idP T n (repW (xs.getD i ([], 0, 0)).2.2 [nL + i])) &&
    bnd nL t.1 && eqP T n [nL + 2 * xs.length] (repW t.2.1 t.1) &&
    idP T n [nL + 2 * xs.length, nL + 2 * xs.length] &&
    Nat.beq ws.length nL && ws.all (bnd (2 * xs.length + 1)) &&
    (List.range nL).all fun j => eqP T n [j] (sh nL (ws.getD j []))

@[expose] noncomputable def blkChk (T : List (List Nat)) (n : Nat) (bl : List (List Nat))
    (gs : List Nat) (bi : List (List Nat)) : Bool :=
  !Nat.beq (bl.headD []).length 0 && bl.all (fun b => Nat.beq b.length (bl.headD []).length) &&
    bl.flatten.all (fun p => Nat.blt p n) && decide bl.flatten.Nodup &&
    Nat.beq bi.length gs.length &&
    (List.range gs.length).all fun k =>
      Nat.beq (bi.getD k []).length bl.length &&
        (List.range bl.length).all fun i =>
          Nat.blt ((bi.getD k []).getD i 0) bl.length &&
            (bl.getD i []).all fun p =>
              (bl.getD ((bi.getD k []).getD i 0) []).contains (tf T (gs.getD k 0) p)

@[expose] noncomputable def fixChk (T : List (List Nat)) (bl : List (List Nat)) (vs : List Nat) :
    Bool :=
  vs.all fun v => bl.all fun b => b.all fun p => b.contains (tf T v p)

@[expose] noncomputable def bp (bi : List (List Nat)) (m : Nat) (w : List Nat) : List Nat :=
  (List.range m).map fun i => wordF (tf bi) w i

@[expose] noncomputable def cmp (x y : List Nat) : List Nat := y.map fun i => x.getD i 0

@[expose] noncomputable def subChk (bi : List (List Nat)) (m nA q : Nat) (Ws : List (List Nat)) :
    Bool :=
  Ws.all (bnd nA) && Nat.beq Ws.length q && decide (Ws.map (bp bi m)).Nodup &&
    (Ws.map (bp bi m)).all fun x => (Ws.map (bp bi m)).all fun y =>
      (Ws.map (bp bi m)).contains (cmp x y)

@[expose] noncomputable def imgChk (bi : List (List Nat)) (m nA r : Nat)
    (spec : List (Nat × List (List Nat))) : Bool :=
  Nat.beq (spec.foldr (fun s a => s.1 * a) 1) r &&
    (List.range spec.length).all (fun i => (List.range i).all fun k =>
      Nat.beq (Nat.gcd (spec.getD i (0, [])).1 (spec.getD k (0, [])).1) 1) &&
    spec.all fun s => subChk bi m nA s.1 s.2

@[expose] noncomputable def pw (x : List Nat) (k i : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) i (fun _ j => x.getD j 0) k

@[expose] noncomputable def cycChk (bi : List (List Nat)) (m nA : Nat) (w : List Nat) : Bool :=
  bnd nA w && (List.range m).all fun i => (List.range m).any fun k =>
    Nat.beq (pw (bp bi m w) k 0) i

@[expose] noncomputable def normW (T : List (List Nat)) (n α r : Nat) (wcj : List (List Nat)) :
    Bool :=
  Nat.beq wcj.length (2 * r) && wcj.all (bnd (2 * r)) &&
    (List.range (2 * r)).all fun i =>
      eqP T n (sh α (wcj.getD i [])) [α + 2 * r, α + i, α + 2 * r]

@[expose] noncomputable def witB (T : List (List Nat)) (n α r : Nat) (b : List Nat) : Bool :=
  b.all (fun p => Nat.blt p n) &&
    (List.range (2 * r)).all (fun a => b.all fun p => b.contains (tf T (α + a) p)) &&
    !b.all fun p => b.contains (tf T (α + 2 * r) p)

@[expose] noncomputable def e2Part (T AB S gw : List (List Nat)) (n : Nat)
    (xs : List (List Nat × Nat × Nat)) (t : List Nat × Nat × Nat) (ws vws : List (List Nat))
    (wit ex : List Nat) (bl bi : List (List Nat)) (sE : Nat) (spec : List (Nat × List (List Nat)))
    (tr : Bool) (cw : List Nat) (alt : Bool) (wcj : List (List Nat)) (b : List Nat) (k : Nat) :
    Bool :=
  bif Nat.beq k 0 then letChk T AB S gw n
  else bif Nat.beq k 1 then alphChk T n (S.length + gw.length) xs t ws
  else bif Nat.beq k 2 then
    vws.all (bnd (2 * xs.length)) &&
      (List.range vws.length).all (fun i =>
        eqP T n [S.length + gw.length + 2 * xs.length + 1 + i]
          (sh (S.length + gw.length) (vws.getD i []))) &&
      commInv (tf T) (List.range n) ((List.range vws.length).map fun i =>
        [S.length + gw.length + 2 * xs.length + 1 + i]) &&
      witChk (tf T) (List.range n) ((List.range vws.length).map fun i =>
        [S.length + gw.length + 2 * xs.length + 1 + i]) wit &&
      blkChk T n bl ((List.range (2 * xs.length + 1)).map fun a => S.length + gw.length + a) bi &&
      fixChk T bl ((List.range vws.length).map fun i =>
        S.length + gw.length + 2 * xs.length + 1 + i)
  else bif Nat.beq k 3 then
    imgChk bi bl.length (2 * xs.length) sE spec &&
      (!tr || cycChk bi bl.length (2 * xs.length) cw) &&
      bif alt then
        normW T n (S.length + gw.length) xs.length wcj &&
          witB T n (S.length + gw.length) xs.length b
      else idP T n [S.length + gw.length + 2 * xs.length]
  else normA (tf T) (List.range n)
    ((List.range (2 * xs.length + 1)).map fun a => [S.length + gw.length + a])
    ((List.range vws.length).map fun i => [S.length + gw.length + 2 * xs.length + 1 + i]) ex
    (k - 4)

@[expose] noncomputable def e2Chk (T AB S gw : List (List Nat)) (n : Nat)
    (xs : List (List Nat × Nat × Nat)) (t : List Nat × Nat × Nat) (ws vws : List (List Nat))
    (wit ex : List Nat) (bl bi : List (List Nat)) (sE : Nat) (spec : List (Nat × List (List Nat)))
    (tr : Bool) (cw : List Nat) (alt : Bool) (wcj : List (List Nat)) (b : List Nat) : Bool :=
  (List.range (2 * xs.length + 5)).all
    (e2Part T AB S gw n xs t ws vws wit ex bl bi sE spec tr cw alt wcj b)

@[expose] noncomputable def l34Part (T AB S gw : List (List Nat)) (n : Nat)
    (xs : List (List Nat × Nat × Nat)) (t : List Nat × Nat × Nat) (ws wcj : List (List Nat))
    (wu wv : List Nat) (rels wxs : List (List Nat)) (k : Nat) : Bool :=
  bif Nat.beq k 0 then letChk T AB S gw n
  else bif Nat.beq k 1 then alphChk T n (S.length + gw.length) xs t ws
  else bif Nat.beq k 2 then
    normW T n (S.length + gw.length) xs.length wcj && bnd (2 * xs.length) wu &&
      bnd (2 * xs.length) wv &&
      eqP T n [S.length + gw.length + 2 * xs.length + 1] (sh (S.length + gw.length) wu) &&
      eqP T n [S.length + gw.length + 2 * xs.length + 2] (sh (S.length + gw.length) wv) &&
      idP T n [S.length + gw.length + 2 * xs.length + 3, S.length + gw.length + 2 * xs.length + 1] &&
      idP T n [S.length + gw.length + 2 * xs.length + 4, S.length + gw.length + 2 * xs.length + 2] &&
      !idP T n [S.length + gw.length + 2 * xs.length + 1]
  else
    rels.all (bnd 4) &&
      rels.all (fun w => idP T n (sh (S.length + gw.length + 2 * xs.length + 1) w)) &&
      Nat.beq wxs.length (2 * xs.length) && wxs.all (bnd 4) &&
      (List.range (2 * xs.length)).all fun i =>
        eqP T n (sh (S.length + gw.length + 2 * xs.length + 1) (wxs.getD i []))
          [S.length + gw.length + i]

@[expose] noncomputable def l34Chk (T AB S gw : List (List Nat)) (n : Nat)
    (xs : List (List Nat × Nat × Nat)) (t : List Nat × Nat × Nat) (ws wcj : List (List Nat))
    (wu wv : List Nat) (rels wxs : List (List Nat)) : Bool :=
  (List.range 4).all (l34Part T AB S gw n xs t ws wcj wu wv rels wxs)

@[expose] noncomputable def m22Chk (T AB S gw : List (List Nat)) (n : Nat)
    (bl bi : List (List Nat)) (wA wB gA gB : List Nat) : Bool :=
  letChk T AB S gw n && Nat.beq bl.length 22 &&
    blkChk T n bl (List.range (S.length + gw.length)) bi &&
    bnd (S.length + gw.length) wA && bnd (S.length + gw.length) wB &&
    (List.range 22).all (fun i => Nat.beq (wordF (tf bi) wA i) (gA.getD i 0)) &&
    (List.range 22).all fun i => Nat.beq (wordF (tf bi) wB i) (gB.getD i 0)

@[expose] noncomputable def triChk (T AB S gw : List (List Nat)) (n : Nat)
    (bl bi : List (List Nat)) (x : List Nat × Nat × Nat) : Bool :=
  letChk T AB S gw n && Nat.beq bl.length 3 &&
    blkChk T n bl (List.range (S.length + gw.length)) bi && bnd (S.length + gw.length) x.1 &&
    eqP T n [S.length + gw.length] (repW x.2.1 x.1) && Nat.beq (x.2.2 % 2) 1 &&
    idP T n (repW x.2.2 [S.length + gw.length]) &&
    !(bl.getD 0 []).contains (tf T (S.length + gw.length) ((bl.getD 0 []).headD 0))

end CFSG.KC.A312M23K

end
