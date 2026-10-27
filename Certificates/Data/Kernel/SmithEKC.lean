module

public import Certificates.Data.Kernel.SmithEKP
public import Certificates.Data.Kernel.SmithEKE
public import Certificates.Data.Kernel.SmithEKT

public section

namespace CFSG.SmithE.K

@[expose] noncomputable def blkC (X b : Nat) : Nat := (X >>> (400 * b)) % 2 ^ 400

@[expose] noncomputable def gathC (Bpk : Nat) (n : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ ih r => blkC Bpk (r % 1024) + (ih (r >>> 10) <<< 400)) n

@[expose] noncomputable def fldsC (n : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun r => r == 0)
    (fun _ ih r => decide (r % 1024 < 693) && ih (r >>> 10)) n

@[expose] noncomputable def rowC (ONE REP ID Bpk : Nat) (Qs : List Nat) (A : List Nat)
    (Ap Rj : Nat) : Bool :=
  lmulP ONE A Ap == ID && fldsC 693 Rj &&
    lmulP ONE A (bmulP ONE Qs (REP * Ap)) == gathC Bpk 693 Rj

@[expose] noncomputable def rowsC (ONE REP ID Bpk : Nat) (Qs : List Nat) (R : Nat → Nat) :
    List (List Nat) → List Nat → Nat → Bool :=
  fun Cr => List.rec (motive := fun _ => List Nat → Nat → Bool) (fun _ _ => true)
    (fun A _ ih Pr j => rowC ONE REP ID Bpk Qs A (Pr.headD 0) (R j) && ih Pr.tail (j + 1)) Cr

@[expose] noncomputable def chkCF (C : List (List Nat)) (R : Nat → Nat) : Bool :=
  let REP := pkW 400 (List.replicate 693 1)
  let Q := C.map (pkW 20)
  C.length == 693 && C.all (fun c => c.length == 20 && c.all fun x => decide (x < 2 ^ 20)) &&
    rowsC (REP * l20) REP (pkW 20 ((List.range 20).map (2 ^ ·))) (pkW 400 Q) (qsOf C) R C Q 0

@[expose] def fldR (R : Nat → Nat) (j a : Nat) : Nat := (R j >>> (10 * a)) % 1024

@[expose] def wordR (R : Nat → Nat) (w : List Nat) (a : Nat) : Nat :=
  w.foldl (fun b j => fldR R j b) a

@[expose] noncomputable def ptWK (R : Nat → Nat) : List (List Nat) → Nat → Bool :=
  fun W => List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun w _ ih a => (w.all (fun j => decide (j < 693)) && wordR R w a == 0) && ih (a + 1)) W

@[expose] noncomputable def pairWK (R : Nat → Nat) (p0 : Nat) :
    List (List Nat) → List Nat → Nat → Bool :=
  fun W => List.rec (motive := fun _ => List Nat → Nat → Bool) (fun _ _ => true)
    (fun w _ ih P l => (CFSG.F4.Native.hermC p0 (P.headD 0) == 0 ||
      (w.all (fun j => decide (j < 693) && fldR R j 0 == 0) && wordR R w l == 1)) &&
      ih P.tail (l + 1)) W

@[expose] noncomputable def vwalk (TC : List Nat) (w : List Nat) (v : Nat) : Nat :=
  w.foldl (fun v k => fld k (c8ap TC v)) v

@[expose] noncomputable def planeWK (TC : List Nat) (w0 : Nat) :
    List (List Nat) → List Nat → Bool :=
  fun W => List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun w _ ih V => (w.all (fun k => decide (k < 693)) && vwalk TC w (V.headD 0) == w0) &&
      ih V.tail) W

end CFSG.SmithE.K
