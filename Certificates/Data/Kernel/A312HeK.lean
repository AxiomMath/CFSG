module

public import Certificates.Data.Kernel.E64F

public section

namespace CFSG.KC.A312HeK

open CFSG.KC.E64F

@[expose] noncomputable def chunkAll (n : Nat) (f : Nat → Bool) (c : Nat) : Bool :=
  (List.range' (1024 * c) 1024).all fun p => !Nat.blt p n || f p

@[expose] noncomputable def invChk (L : Nat → Nat → Nat) (n nL l c : Nat) : Bool :=
  chunkAll n (fun p => Nat.beq (L (nL + l) (L l p)) p) c

@[expose] noncomputable def repW (k : Nat) (w : List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) [] (fun _ acc => w ++ acc) k

@[expose] noncomputable def invW (nL : Nat) (w : List Nat) : List Nat :=
  w.reverse.map fun l => nL + l

@[expose] noncomputable def qW (x : List Nat × Nat × Nat) : List Nat := repW x.2.1 x.1

@[expose] noncomputable def qWi (nL : Nat) (x : List Nat × Nat × Nat) : List Nat :=
  repW x.2.1 (invW nL x.1)

@[expose] noncomputable def alphaW (nL : Nat) (xs : List (List Nat × Nat × Nat))
    (t : List Nat × Nat × Nat) : List (List Nat) :=
  xs.map qW ++ xs.map (qWi nL) ++ [qW t]

@[expose] noncomputable def expW (A : List (List Nat)) (u : List Nat) : List Nat :=
  u.flatMap fun a => A.getD a []

@[expose] noncomputable def eqB (L : Nat → Nat → Nat) (B : List Nat) (u v : List Nat) : Bool :=
  B.all fun p => Nat.beq (wordF L u p) (wordF L v p)

@[expose] noncomputable def idB (L : Nat → Nat → Nat) (B : List Nat) (u : List Nat) : Bool :=
  B.all fun p => Nat.beq (wordF L u p) p

@[expose] noncomputable def subW (V : List (List Nat)) (e : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun v _ ih e => (bif Nat.beq (e % 2) 1 then v else []) ++ ih (e / 2)) V e

@[expose] noncomputable def bnd (m : Nat) (w : List Nat) : Bool := w.all fun l => Nat.blt l m

@[expose] noncomputable def idxChk (L : Nat → Nat → Nat) (B : List Nat) (nL : Nat)
    (xs : List (List Nat × Nat × Nat)) (t : List Nat × Nat × Nat) (ws : List (List Nat)) : Bool :=
  xs.all (fun x => bnd nL x.1 && Nat.beq (x.2.2 % 2) 1 && idB L B (repW x.2.2 (qW x))) &&
    bnd nL t.1 && idB L B (repW 2 (qW t)) &&
    Nat.beq ws.length nL && ws.all (bnd (2 * xs.length + 1)) &&
    (List.range nL).all fun j => eqB L B (expW (alphaW nL xs t) (ws.getD j [])) [j]

@[expose] noncomputable def pt (pts : List Nat) (i : Nat) : Nat := pts.getD i 0

@[expose] noncomputable def sixChk (L : Nat → Nat → Nat) (n : Nat) (A : List (List Nat))
    (pts : List Nat) (w1 w2 : List Nat) : Bool :=
  Nat.beq pts.length 6 && decide pts.Nodup && pts.all (fun p => Nat.blt p n) &&
    A.all (fun g => pts.all fun p => pts.contains (wordF L g p)) &&
    bnd A.length w1 && bnd A.length w2 &&
    (List.range 6).all (fun i =>
      Nat.beq (wordF L (expW A w1) (pt pts i)) (pt pts ((i + 1) % 6))) &&
    (List.range 6).all fun i =>
      Nat.beq (wordF L (expW A w2) (pt pts i))
        (pt pts (bif Nat.beq i 0 then 1 else bif Nat.beq i 1 then 0 else i))

@[expose] noncomputable def normA (L : Nat → Nat → Nat) (B : List Nat) (A V : List (List Nat))
    (ex : List Nat) (a : Nat) : Bool :=
  (List.range V.length).all fun i =>
    let e := ex.getD (V.length * a + i) 0
    Nat.blt e (2 ^ V.length) && eqB L B (V.getD i [] ++ A.getD a []) (A.getD a [] ++ subW V e)

@[expose] noncomputable def commInv (L : Nat → Nat → Nat) (B : List Nat) (V : List (List Nat)) :
    Bool :=
  V.all (fun v => idB L B (v ++ v)) &&
    (List.range V.length).all fun i => (List.range i).all fun k =>
      eqB L B (V.getD i [] ++ V.getD k []) (V.getD k [] ++ V.getD i [])

@[expose] noncomputable def witChk (L : Nat → Nat → Nat) (B : List Nat) (V : List (List Nat))
    (wit : List Nat) : Bool :=
  Nat.beq wit.length (2 ^ V.length - 1) &&
    (List.range wit.length).all fun i =>
      let q := B.getD (wit.getD i 0) 0
      Nat.blt (wit.getD i 0) B.length && !Nat.beq (wordF L (subW V (i + 1)) q) q

@[expose] noncomputable def hatPart (L : Nat → Nat → Nat) (n : Nat) (B : List Nat) (nL : Nat)
    (xs : List (List Nat × Nat × Nat)) (t : List Nat × Nat × Nat) (ws : List (List Nat))
    (pts : List Nat) (w1 w2 : List Nat) (vws : List (List Nat)) (wit ex : List Nat) (k : Nat) :
    Bool :=
  let A := alphaW nL xs t
  let V := vws.map (expW A)
  bif Nat.beq k 0 then
    idxChk L B nL xs t ws && sixChk L n A pts w1 w2 &&
      Nat.beq vws.length 6 && vws.all (bnd (2 * xs.length)) &&
      V.all (fun v => pts.all fun p => Nat.beq (wordF L v p) p) && commInv L B V &&
      Nat.beq ex.length (6 * A.length)
  else bif Nat.blt k (A.length + 1) then normA L B A V ex (k - 1)
  else witChk L B V wit

@[expose] noncomputable def hatChk (L : Nat → Nat → Nat) (n : Nat) (B : List Nat) (nL : Nat)
    (xs : List (List Nat × Nat × Nat)) (t : List Nat × Nat × Nat) (ws : List (List Nat))
    (pts : List Nat) (w1 w2 : List Nat) (vws : List (List Nat)) (wit ex : List Nat) : Bool :=
  (List.range (2 * xs.length + 3)).all (hatPart L n B nL xs t ws pts w1 w2 vws wit ex)

@[expose] noncomputable def bit (c k : Nat) : Bool := Nat.beq (c / 2 ^ k % 2) 1

@[expose] noncomputable def rowSum (C : List Nat) (idx : List Nat) (e : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun i _ ih e => Nat.xor (bif Nat.beq (e % 2) 1 then C.getD i 0 else 0) (ih (e / 2))) idx e

@[expose] noncomputable def maskOf (idx : List Nat) : Nat :=
  idx.foldr (fun i acc => Nat.lor (2 ^ i) acc) 0

@[expose] noncomputable def gramOK (C : List Nat) (idx : List Nat) : Bool :=
  (List.range (2 ^ idx.length - 1)).all fun i =>
    !Nat.beq (Nat.land (rowSum C idx (i + 1)) (maskOf idx)) 0

@[expose] noncomputable def relChk (L : Nat → Nat → Nat) (B : List Nat) (W : List (List Nat))
    (zw : List Nat) (sq C : List Nat) : Bool :=
  Nat.beq sq.length W.length && Nat.beq C.length W.length &&
    (List.range W.length).all (fun i =>
      let a := W.getD i []
      Nat.blt (C.getD i 0) (2 ^ W.length) && !bit (C.getD i 0) i &&
        (bif Nat.beq (sq.getD i 0) 0 then idB L B (a ++ a) else eqB L B (a ++ a) zw) &&
        (List.range i).all fun k =>
          let b := W.getD k []
          Bool.beq (bit (C.getD i 0) k) (bit (C.getD k 0) i) &&
            (bif bit (C.getD i 0) k then eqB L B (a ++ b) (zw ++ b ++ a)
              else eqB L B (a ++ b) (b ++ a)))

@[expose] noncomputable def extPart (L : Nat → Nat → Nat) (B : List Nat) (nL : Nat)
    (xs : List (List Nat × Nat × Nat)) (t : List Nat × Nat × Nat) (ws : List (List Nat))
    (W : List (List Nat)) (zw : List Nat) (sq C idx ex : List Nat) (k : Nat) : Bool :=
  bif Nat.beq k 0 then
    idxChk L B nL xs t ws && W.all (bnd nL) && bnd nL zw && W.contains zw &&
      !idB L B zw && idB L B (zw ++ zw) && W.all (fun a => eqB L B (a ++ zw) (zw ++ a)) &&
      relChk L B W zw sq C && bnd W.length idx &&
      (List.range W.length).all (fun i => idx.contains i || W.getD i [] == zw) &&
      gramOK C idx && Nat.beq ex.length (W.length * (2 * xs.length + 1))
  else normA L B (alphaW nL xs t) W ex (k - 1)

@[expose] noncomputable def extChk (L : Nat → Nat → Nat) (B : List Nat) (nL : Nat)
    (xs : List (List Nat × Nat × Nat)) (t : List Nat × Nat × Nat) (ws : List (List Nat))
    (W : List (List Nat)) (zw : List Nat) (sq C idx ex : List Nat) : Bool :=
  (List.range (2 * xs.length + 2)).all (extPart L B nL xs t ws W zw sq C idx ex)

end CFSG.KC.A312HeK

end
