module

public import Certificates.Data.Kernel.HeisN

public section

namespace CFSG.KC.F4T

open CFSG.LieType.SeitzGeneration.HeisSmall CFSG.KC.HeisN

@[expose] def tabT : Nat := 2625168384

@[expose] def mT (a b : Nat) : Nat := Nat.land (Nat.shiftRight tabT (2 * (4 * a + b))) 3

@[expose] def aT (a b : Nat) : Nat := Nat.xor a b

@[expose] def dotT (a0 a1 a2 b0 b1 b2 : Nat) : Nat := aT (aT (mT a0 b0) (mT a1 b1)) (mT a2 b2)

@[expose] def mMulT (A B : M3 Nat) : M3 Nat :=
  ⟨dotT A.a00 A.a01 A.a02 B.a00 B.a10 B.a20, dotT A.a00 A.a01 A.a02 B.a01 B.a11 B.a21,
    dotT A.a00 A.a01 A.a02 B.a02 B.a12 B.a22,
    dotT A.a10 A.a11 A.a12 B.a00 B.a10 B.a20, dotT A.a10 A.a11 A.a12 B.a01 B.a11 B.a21,
    dotT A.a10 A.a11 A.a12 B.a02 B.a12 B.a22,
    dotT A.a20 A.a21 A.a22 B.a00 B.a10 B.a20, dotT A.a20 A.a21 A.a22 B.a01 B.a11 B.a21,
    dotT A.a20 A.a21 A.a22 B.a02 B.a12 B.a22⟩

@[expose] def detT (A : M3 Nat) : Nat :=
  aT (aT (aT (mT (mT A.a00 A.a11) A.a22) (mT (mT A.a00 A.a12) A.a21))
    (aT (mT (mT A.a01 A.a10) A.a22) (mT (mT A.a01 A.a12) A.a20)))
    (aT (mT (mT A.a02 A.a10) A.a21) (mT (mT A.a02 A.a11) A.a20))

@[expose] def evalT (gens : List (M3 Nat)) (w : List Nat) : M3 Nat :=
  w.foldl (fun acc k => mMulT acc (gens.getD k mOne)) mOne

@[expose] def pow4T (w : M3 Nat) : M3 Nat := mMulT (mMulT w w) (mMulT w w)

@[expose] def codeOK (l : List Nat) : Bool := Nat.beq l.length 9 && l.all fun x => Nat.blt x 4

@[expose] def xdT : M3 Nat := ⟨1, 0, 0, 0, 3, 0, 0, 0, 2⟩

@[expose] def xd2T : M3 Nat := ⟨1, 0, 0, 0, 2, 0, 0, 0, 3⟩

@[expose] def zsT : M3 Nat := ⟨2, 0, 0, 0, 2, 0, 0, 0, 2⟩

@[expose] def zs2T : M3 Nat := ⟨3, 0, 0, 0, 3, 0, 0, 0, 3⟩

@[expose] def wmT (μ : Nat) : M3 Nat := ⟨0, 0, μ, 1, 0, 0, 0, 1, 0⟩

@[expose] def wm2T (μ : Nat) : M3 Nat := ⟨0, μ, 0, 0, 0, μ, 1, 0, 0⟩

@[expose] def esT : List (M3 Nat) :=
  [⟨1, 1, 0, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 1, 0, 1, 0, 0, 0, 1⟩, ⟨1, 0, 0, 1, 1, 0, 0, 0, 1⟩,
    ⟨1, 0, 0, 0, 1, 1, 0, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 1, 0, 1⟩, ⟨1, 0, 0, 0, 1, 0, 0, 1, 1⟩]

@[expose] def gens7T : List (M3 Nat) := xdT :: esT

@[expose] def w6OK (gens : List (M3 Nat)) (ws : List (List Nat)) : Bool :=
  Nat.beq ws.length 6 && (ws.zip esT).all fun p => mEq (evalT gens p.1) p.2

@[expose] def gensT3 (μ : Nat) (A : M3 Nat) : List (M3 Nat) :=
  [xdT, xd2T, wmT μ, wm2T μ, zsT, zs2T, A]

@[expose] def isRootT (A : M3 Nat) : Bool :=
  Nat.beq A.a00 1 && Nat.beq A.a11 1 && Nat.beq A.a22 1 &&
    Nat.beq ([A.a01, A.a02, A.a10, A.a12, A.a20, A.a21].filter fun c => !Nat.beq c 0).length 1

@[expose] def t3RowOK (code : List Nat) (w1 wo wo2 : List (List Nat)) : Bool :=
  let A := matN code
  codeOK code && w6OK (gensT3 2 A) wo && w6OK (gensT3 3 A) wo2 &&
    (!isRootT A || w6OK (gensT3 1 A) w1)

@[expose] def t3RowsOK (codes : List (List Nat)) (w1 wo wo2 : List (List (List Nat))) : Bool :=
  Nat.beq w1.length codes.length && Nat.beq wo.length codes.length &&
    Nat.beq wo2.length codes.length &&
    (codes.zip (w1.zip (wo.zip wo2))).all fun p => t3RowOK p.1 p.2.1 p.2.2.1 p.2.2.2

@[expose] def ptsT : List (List Nat) :=
  ((List.range 16).map fun n => [1, n / 4, n % 4]) ++ ((List.range 4).map fun c => [0, 1, c]) ++
    [[0, 0, 1]]

@[expose] def vecsT : List (List Nat) :=
  (List.range 63).map fun n => [(n + 1) / 16, (n + 1) / 4 % 4, (n + 1) % 4]

@[expose] def outerT (v w : List Nat) : M3 Nat :=
  let v0 := v.getD 0 0
  let v1 := v.getD 1 0
  let v2 := v.getD 2 0
  let w0 := w.getD 0 0
  let w1 := w.getD 1 0
  let w2 := w.getD 2 0
  ⟨aT 1 (mT v0 w0), mT v0 w1, mT v0 w2, mT v1 w0, aT 1 (mT v1 w1), mT v1 w2, mT v2 w0, mT v2 w1,
    aT 1 (mT v2 w2)⟩

@[expose] def invsAt (v : List Nat) : List (M3 Nat) :=
  (vecsT.filter fun w => Nat.beq (dotT (v.getD 0 0) (v.getD 1 0) (v.getD 2 0) (w.getD 0 0)
    (w.getD 1 0) (w.getD 2 0)) 0).map (outerT v)

@[expose] def invsT : List (M3 Nat) := ptsT.flatMap invsAt

@[expose] def lettersT (A : M3 Nat) : List (M3 Nat) :=
  [A, mMulT (mMulT xdT A) xd2T, mMulT (mMulT xd2T A) xdT]

@[expose] def words3T (A : M3 Nat) : List (M3 Nat) :=
  let L := lettersT A
  L ++ L.flatMap (fun a => L.map fun b => mMulT a b) ++
    L.flatMap (fun a => L.flatMap fun b => L.map fun c => mMulT (mMulT a b) c)

@[expose] def wit1OK (rows : List (List Nat)) (A : M3 Nat) (x : Nat × Nat) : Bool :=
  cond (Nat.beq x.1 0) (Nat.blt x.2 rows.length && mEq A (matN (rows.getD x.2 [])))
    (!mEq (pow4T ((words3T A).getD x.2 mOne)) mOne)

@[expose] def witOK (rows : List (List Nat)) (invs : List (M3 Nat)) (wits : List (Nat × Nat)) :
    Bool :=
  Nat.beq invs.length wits.length && (invs.zip wits).all fun p => wit1OK rows p.1 p.2

@[expose] def ptT (x y z : Nat) : Nat :=
  cond (Nat.beq x 0)
    (cond (Nat.beq y 0) 0 (1 + mT (mT y y) z))
    (5 + 4 * mT (mT x x) y + mT (mT x x) z)

@[expose] def imgT (A : M3 Nat) (v : List Nat) : Nat :=
  let v0 := v.getD 0 0
  let v1 := v.getD 1 0
  let v2 := v.getD 2 0
  ptT (dotT A.a00 A.a01 A.a02 v0 v1 v2) (dotT A.a10 A.a11 A.a12 v0 v1 v2)
    (dotT A.a20 A.a21 A.a22 v0 v1 v2)

@[expose] def hmaskT (A : M3 Nat) (Om : List (List Nat)) : Nat :=
  Om.foldl (fun m v => Nat.lor m (Nat.shiftLeft 1 (imgT A v))) 0

@[expose] def inT (l : List Nat) (x : Nat) : Bool := l.any (Nat.beq x)

@[expose] def closeOK (Om : List (List Nat)) (reps : List (List Nat)) (ms : List Nat) : Bool :=
  Nat.beq reps.length ms.length && inT ms (hmaskT mOne Om) &&
    (reps.zip ms).all fun p =>
      let R := matN p.1
      codeOK p.1 && Nat.beq (detT R) 1 && Nat.beq (hmaskT R Om) p.2 &&
        gens7T.all fun g => inT ms (hmaskT (mMulT g R) Om)

@[expose] def t4WordsOK (Om : List (List Nat)) (r : List Nat) (reps : List (List Nat))
    (ws : List (List (List Nat))) : Bool :=
  let rm := matN r
  codeOK r && Nat.beq (detT rm) 1 && Nat.beq (hmaskT rm Om) (hmaskT mOne Om) &&
    Nat.beq reps.length ws.length &&
    (reps.zip ws).all fun p => codeOK p.1 && w6OK [xdT, wmT 1, zsT, rm, matN p.1] p.2

@[expose] def chunkT {α : Type} (n k : Nat) (l : List α) : List α := (l.drop (n * k)).take n

@[expose] def inPT (Om : List (List Nat)) (A : M3 Nat) : Bool :=
  Nat.beq (detT A) 1 && Nat.beq (hmaskT A Om) (hmaskT mOne Om)

@[expose] def levelsT : List (Nat × Nat) :=
  (List.range 4).flatMap fun l => (List.range (5 - l)).map fun d => (l, l + 1 + d)

@[expose] def stepOK (Om : List (List Nat)) (r : M3 Nat) (lp : Nat × Nat) : Bool :=
  (List.range lp.1).all (fun i => Nat.beq (imgT r (Om.getD i [])) (imgT mOne (Om.getD i []))) &&
    Nat.beq (imgT r (Om.getD lp.1 [])) (imgT mOne (Om.getD lp.2 []))

@[expose] def chainOK (Om : List (List Nat)) (g1 g2 : List Nat) (ws : List (List Nat)) : Bool :=
  let gs := [matN g1, matN g2]
  Nat.beq Om.length 6 && codeOK g1 && codeOK g2 && inPT Om (matN g1) && inPT Om (matN g2) &&
    Nat.beq ws.length levelsT.length &&
    (ws.zip levelsT).all fun p => stepOK Om (evalT gs p.1) p.2

@[expose] def nonRootOK (Om : List (List Nat)) (g1 g2 code : List Nat) (ws : List (List Nat)) :
    Bool :=
  let A := matN code
  let gens := [xdT, wmT 1, zsT, A]
  codeOK code && inPT Om A && Nat.beq ws.length 2 &&
    mEq (evalT gens (ws.getD 0 [])) (matN g1) && mEq (evalT gens (ws.getD 1 [])) (matN g2)

@[expose] def nonRootsOK (oms : List (List (List Nat))) (gks : List (List (List Nat)))
    (codes : List (List Nat)) (idx : List Nat) (ws : List (List (List Nat))) : Bool :=
  Nat.beq idx.length codes.length && Nat.beq ws.length codes.length &&
    (codes.zip (idx.zip ws)).all fun p =>
      isRootT (matN p.1) || (Nat.blt p.2.1 6 &&
        let gk := gks.getD p.2.1 []
        nonRootOK (oms.getD p.2.1 []) (gk.getD 0 []) (gk.getD 1 []) p.1 p.2.2)

end CFSG.KC.F4T
