module

public import Certificates.Data.Kernel.G2Three.Sec1T3

public section

namespace CFSG.KD.G2Three.Sec1T3

open CFSG.KC.Loop

@[expose] noncomputable def mulE (P x y : Nat) : Nat := atR (rowT P x) y

@[expose] noncomputable def lstM (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ acc => Nat.lor (Nat.shiftLeft 1 x) acc) l

@[expose] noncomputable def stepK (C : Nat) (gs : List Nat) (M : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) M (fun g _ acc => Nat.lor acc (imgR (rowT C g) M)) gs

@[expose] noncomputable def closK (C : Nat) (gs : List Nat) (R : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 1 (fun _ acc => strictN acc (stepK C gs)) R

@[expose] noncomputable def closOK (C : Nat) (gs : List Nat) (R : Nat) : Bool :=
  strictB (closK C gs R) fun M => Nat.beq (stepK C gs M) M

@[expose] noncomputable def cenE (P C X y : Nat) : Nat :=
  strictN X fun X => strictN y fun y =>
    Nat.rec (motive := fun _ => Nat) 0 (fun i acc =>
      nIf(bAnd(hasB X i, Nat.beq (atR (rowT P i) y) (atR (rowT C i) y)),
        Nat.lor acc (Nat.shiftLeft 1 i), acc)) 128

@[expose] noncomputable def involM (Q X : Nat) : Nat :=
  strictN X fun X => Nat.rec (motive := fun _ => Nat) 0 (fun i acc =>
    nIf(bAnd(hasB X i, bAnd(Nat.blt 0 i, Nat.beq (atR Q i) 0)),
      Nat.lor acc (Nat.shiftLeft 1 i), acc)) 128

@[expose] noncomputable def clsE (P C V X y : Nat) : Nat :=
  strictN X fun X => strictN y fun y =>
    Nat.rec (motive := fun _ => Nat) 0 (fun i acc =>
      nIf(hasB X i, Nat.lor acc (Nat.shiftLeft 1 (conjR (rowT P i) (rowT C (atR V i)) y)), acc))
      128

@[expose] noncomputable def prodM (C A B : Nat) : Nat :=
  strictN A fun A => strictN B fun B =>
    Nat.rec (motive := fun _ => Nat) 0 (fun b acc =>
      nIf(hasB B b, Nat.lor acc (imgR (rowT C b) A), acc)) 128

@[expose] noncomputable def lprodM (P B A : Nat) : Nat :=
  strictN A fun A => strictN B fun B =>
    Nat.rec (motive := fun _ => Nat) 0 (fun b acc =>
      nIf(hasB B b, Nat.lor acc (imgR (rowT P b) A), acc)) 128

@[expose] noncomputable def permB (P C A B : Nat) : Bool :=
  Nat.beq (prodM C A B) (lprodM P B A)

@[expose] noncomputable def elemAbK (P C Q X : Nat) : Bool :=
  strictB X fun X => allBelow 128 2 fun x =>
    bIf(hasB X x, bAnd(Nat.beq (atR Q x) 0, Nat.beq (cenE P C X x) X), true)

@[expose] noncomputable def powE (P x k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun _ acc => mulE P acc x) k

@[expose] noncomputable def d8M (u v : Nat) : Nat :=
  (fun i j => nIf(Nat.blt u 4,
      nIf(Nat.blt v 4, Nat.mod (Nat.add i j) 4, Nat.add 4 (Nat.mod (Nat.sub (Nat.add j 4) i) 4)),
      nIf(Nat.blt v 4, Nat.add 4 (Nat.mod (Nat.add i j) 4), Nat.mod (Nat.sub (Nat.add j 4) i) 4)))
    (Nat.mod u 4) (Nat.mod v 4)

@[expose] noncomputable def d8I (P r s k : Nat) : Nat :=
  nIf(Nat.blt k 4, powE P r k, mulE P s (powE P r (Nat.sub k 4)))

@[expose] noncomputable def d8K (P r s Dm : Nat) : Bool :=
  bAnd(allBelow 64 1 fun uv => (fun u v =>
      Nat.beq (d8I P r s (d8M u v)) (mulE P (d8I P r s u) (d8I P r s v)))
    (Nat.shiftRight uv 3) (Nat.land uv 7),
  bAnd(Nat.beq (Nat.rec (motive := fun _ => Nat) 0
      (fun k acc => Nat.lor acc (Nat.shiftLeft 1 (d8I P r s k))) 8) Dm,
    Nat.beq (pop Dm) 8))

@[expose] noncomputable def z2d8K (P C Q X c g1 g2 R : Nat) : Bool :=
  bAnd(closOK C [g1, g2] R, strictB (closK C [g1, g2] R) fun Dm => strictB c fun c =>
    bAnd(Nat.blt 0 c, bAnd(Nat.beq (atR Q c) 0,
    bAnd(Nat.beq (Nat.lor Dm (imgR (rowT P c) Dm)) X, bAnd(Bool.not' (hasB Dm c),
    bAnd(Nat.beq (cenE P C Dm c) Dm, d8K P g1 g2 Dm))))))

@[expose] noncomputable def hdL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ _ => x) l

@[expose] noncomputable def unionL (cl : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun c _ acc => Nat.lor (lstM c) acc) cl

@[expose] noncomputable def distB (ms : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun m t ih => bAnd(
    List.rec (motive := fun _ => Bool) true (fun m' _ ih2 =>
      bAnd(Bool.not' (Nat.beq m m'), ih2)) t, ih)) ms

@[expose] noncomputable def lstMs (cl : List (List Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun c _ acc => lstM c :: acc) cl

@[expose] noncomputable def listsOK (P C V T I : Nat) (cl : List (List Nat)) : Bool :=
  bAnd(List.rec (motive := fun _ => Bool) true (fun c _ ih => bAnd(
      List.rec (motive := fun _ => Bool) false (fun x _ _ =>
        bAnd(hasB I x, Nat.beq (lstM c) (clsE P C V T x))) c, ih)) cl,
    bAnd(Nat.beq (Nat.land I (unionL cl)) I, distB (lstMs cl)))

@[expose] noncomputable def clsMs (P C V T : Nat) (rs : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun r _ acc => clsE P C V T r :: acc) rs

@[expose] noncomputable def unionM (ms : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun m _ acc => Nat.lor m acc) ms

@[expose] noncomputable def repsOK (P C V T I : Nat) (rs : List Nat) : Bool :=
  bAnd(List.rec (motive := fun _ => Bool) true (fun r _ ih => bAnd(hasB I r, ih)) rs,
    (fun ms => bAnd(Nat.beq (Nat.land I (unionM ms)) I, distB ms)) (clsMs P C V T rs))

@[expose] noncomputable def rel11K (P C V Q a1 b1 a2 b2 h0 sg : Nat) : Bool :=
  (fun z => bAnd(Nat.beq (atR Q z) 0, bAnd(Nat.beq (atR Q h0) 0, bAnd(Nat.beq (atR Q sg) 0,
    bAnd(Nat.beq (atR Q a1) z, bAnd(Nat.beq (atR Q a2) z, bAnd(Nat.beq (atR Q b2) z,
    bAnd(Nat.beq (commE P C V a1 b1) z, bAnd(Nat.beq (commE P C V a2 b2) z,
    bAnd(Nat.beq (commE P C V a1 h0) (mulE P b1 z), bAnd(Nat.beq (commE P C V a2 h0) (mulE P b2 z),
    bAnd(Nat.beq (commE P C V b1 h0) z, bAnd(Nat.beq (commE P C V b2 h0) z,
    bAnd(Nat.beq (commE P C V a1 sg) (mulE P (mulE P a1 a2) z),
    bAnd(Nat.beq (commE P C V a2 sg) (mulE P (mulE P a1 a2) z),
    bAnd(Nat.beq (commE P C V b1 sg) (mulE P (mulE P b1 b2) z),
    bAnd(Nat.beq (commE P C V b2 sg) (mulE P (mulE P b1 b2) z),
    bAnd(Nat.beq (commE P C V h0 sg) z,
    bAnd(Nat.beq (commE P C V a1 a2) 0, bAnd(Nat.beq (commE P C V a1 b2) 0,
    bAnd(Nat.beq (commE P C V b1 a2) 0, Nat.beq (commE P C V b1 b2) 0)))))))))))))))))))))
    (atR Q b1)

@[expose] noncomputable def f11K (P C V Q a1 b1 a2 b2 h0 sg R : Nat) : Bool :=
  bAnd(rel11K P C V Q a1 b1 a2 b2 h0 sg,
  bAnd(closOK C [a1, b1, a2, b2, h0] R, bAnd(Nat.beq (pop (closK C [a1, b1, a2, b2, h0] R)) 64,
  bAnd(closOK C [a1, b1, a2, b2, h0, sg] R,
    Nat.beq (pop (closK C [a1, b1, a2, b2, h0, sg] R)) 128))))

@[expose] noncomputable def cls12K (P z a1 b1 a2 b2 h0 : Nat) : List (List Nat) :=
  (fun m2 m3 m4 m5 =>
    [[z],
     [m2 b1 b2, m3 b1 b2 z],
     [m2 a1 a2, m3 a1 a2 z, m4 a1 b1 a2 b2, m5 a1 b1 a2 b2 z],
     [m2 a1 b2, m3 a1 b2 z, m3 a1 b1 b2, m4 a1 b1 b2 z],
     [m2 b1 a2, m3 b1 a2 z, m3 b1 a2 b2, m4 b1 a2 b2 z],
     [m3 a1 b1 a2, m4 a1 b1 a2 z, m3 a1 a2 b2, m4 a1 a2 b2 z],
     [h0, m2 h0 z, m2 b1 h0, m3 b1 h0 z, m2 b2 h0, m3 b2 h0 z, m3 b1 b2 h0, m4 b1 b2 h0 z]])
    (fun x y => mulE P x y) (fun x y w => mulE P (mulE P x y) w)
    (fun x y w u => mulE P (mulE P (mulE P x y) w) u)
    (fun x y w u v => mulE P (mulE P (mulE P (mulE P x y) w) u) v)

@[expose] noncomputable def f12ClassK (P C V Q S a1 b1 a2 b2 h0 : Nat) : Bool :=
  strictB (involM Q S) fun I => listsOK P C V S I (cls12K P (atR Q b1) a1 b1 a2 b2 h0)

@[expose] noncomputable def f12CentK (P C Q S a1 b1 a2 b2 h0 R : Nat) : Bool :=
  (fun z => bAnd(Nat.beq (cenE P C S z) S,
    bAnd(closOK C [mulE P a1 a2, b1, b2, h0] R,
    bAnd(Nat.beq (cenE P C S (mulE P b1 b2)) (closK C [mulE P a1 a2, b1, b2, h0] R),
    bAnd(closOK C [mulE P b1 b2, h0, z] R, strictB (closK C [mulE P b1 b2, h0, z] R) fun E =>
      bAnd(Nat.beq (cenE P C S h0) E, bAnd(elemAbK P C Q E, Nat.beq (pop E) 8)))))))
    (atR Q b1)

@[expose] noncomputable def f12DecK (P C Q S a1 b1 a2 b2 R : Nat) : Bool :=
  (fun d => bAnd(d (mulE P a1 a2) a1 (mulE P b1 b2), bAnd(d (mulE P a1 b2) a1 (mulE P b1 a2),
    bAnd(d (mulE P b1 a2) b1 (mulE P a1 b2), d (mulE P (mulE P a1 b1) a2) a2 (mulE P a1 b2)))))
    (fun c g1 g2 => z2d8K P C Q (cenE P C S c) c g1 g2 R)

@[expose] noncomputable def f12K (P C V Q a1 b1 a2 b2 h0 R : Nat) : Bool :=
  bAnd(closOK C [a1, b1, a2, b2, h0] R, strictB (closK C [a1, b1, a2, b2, h0] R) fun S =>
    bAnd(f12ClassK P C V Q S a1 b1 a2 b2 h0, bAnd(f12CentK P C Q S a1 b1 a2 b2 h0 R,
      f12DecK P C Q S a1 b1 a2 b2 R)))

@[expose] noncomputable def f13CosetK (P C V Q S a1 b1 a2 b2 sg R : Nat) : Bool :=
  (fun F => bAnd(closOK C F R, strictB (cenE P C S sg) fun cs =>
    bAnd(Nat.beq cs (closK C F R), strictB (imgR (rowT C sg) cs) fun cg =>
      bAnd(Nat.beq (involM Q (imgR (rowT C sg) S)) cg, Nat.beq cg (clsE P C V S sg)))))
    [mulE P a1 a2, mulE P b1 b2, atR Q b1]

@[expose] noncomputable def reps13K (P z a1 b1 a2 b2 h0 sg : Nat) : List Nat :=
  [z, mulE P b1 b2, mulE P a1 a2, mulE P a1 b2, mulE P (mulE P a1 b1) a2, h0, sg]

@[expose] noncomputable def f13ClassK (P C V Q Ss a1 b1 a2 b2 h0 sg : Nat) : Bool :=
  strictB (involM Q Ss) fun I => repsOK P C V Ss I (reps13K P (atR Q b1) a1 b1 a2 b2 h0 sg)

@[expose] noncomputable def supCK (P C S Ss y : Nat) (gs : List Nat) (R : Nat) : Bool :=
  bAnd(closOK C gs R, strictB (closK C gs R) fun Y => strictB (cenE P C S y) fun A =>
    bAnd(permB P C A Y, Nat.beq (cenE P C Ss y) (prodM C A Y)))

@[expose] noncomputable def f13CentK (P C Q S Ss a1 b1 a2 b2 h0 sg R : Nat) : Bool :=
  bAnd(Nat.beq (cenE P C Ss (atR Q b1)) Ss,
  bAnd(supCK P C S Ss (mulE P b1 b2) [sg] R, bAnd(supCK P C S Ss (mulE P a1 a2) [sg] R,
  bAnd(Nat.beq (cenE P C Ss (mulE P a1 b2)) (cenE P C S (mulE P a1 b2)),
  bAnd(supCK P C S Ss (mulE P (mulE P a1 b1) a2) [mulE P h0 sg] R,
  bAnd(supCK P C S Ss h0 [mulE P b1 sg] R, supCK P C S Ss sg [sg] R))))))

@[expose] noncomputable def f13K (P C V Q a1 b1 a2 b2 h0 sg R : Nat) : Bool :=
  bAnd(closOK C [a1, b1, a2, b2, h0] R, bAnd(closOK C [a1, b1, a2, b2, h0, sg] R,
    strictB (closK C [a1, b1, a2, b2, h0] R) fun S =>
    strictB (closK C [a1, b1, a2, b2, h0, sg] R) fun Ss =>
      bAnd(f13CosetK P C V Q S a1 b1 a2 b2 sg R, bAnd(f13ClassK P C V Q Ss a1 b1 a2 b2 h0 sg,
        f13CentK P C Q S Ss a1 b1 a2 b2 h0 sg R))))

end CFSG.KD.G2Three.Sec1T3
