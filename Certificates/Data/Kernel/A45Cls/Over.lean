module

public import Certificates.Data.Kernel.A45Cls.Pock

public section

namespace CFSG.KC.A45Cls

open CFSG.KC.Enum CFSG.KS CFSG.KC.OrbFind

@[expose] noncomputable def eqP (n w P Q : Nat) : Bool := eq22 n w (mask w) P (pidn n w) Q (pidn n w)

@[expose] noncomputable def inPts (n w N : Nat) (T : Nat → Nat) (v : Nat) : Bool :=
  exN N fun j => eqP n w (T j) v

@[expose] noncomputable def nrmP (n w ng N : Nat) (G T : Nat → Nat) (c : Nat) : Bool :=
  allN ng fun k => exN N fun j => eq22 n w (mask w) c (G k) (T j) c

@[expose] noncomputable def cosK (n w ng N nu : Nat) (G T U : Nat → Nat) (c : Nat) : Bool :=
  !nrmP n w ng N G T c || inPts n w N T c || !inPts n w N T (pcomp n w (mask w) c c) ||
    exN nu fun m => exN N fun j => eq22 n w (mask w) c (pidn n w) (T j) (U m)

@[expose] noncomputable def zcK (n w ng N : Nat) (G T : Nat → Nat) (z : Nat) : Bool :=
  allN N fun j => !(allN ng fun k => eq22 n w (mask w) (T j) (G k) (G k) (T j)) ||
    isIdK n w (T j) || eqP n w (T j) z

@[expose] noncomputable def tP (n w N : Nat) (T : Nat → Nat) (u p : Nat) : Nat :=
  nIf(Nat.blt p N, T p, pcomp n w (mask w) (T (p - N)) u)

@[expose] noncomputable def tPI (n w N : Nat) (T I : Nat → Nat) (ui p : Nat) : Nat :=
  nIf(Nat.blt p N, T (I p), pcomp n w (mask w) ui (T (I (p - N))))

@[expose] noncomputable def cjP (n w N : Nat) (T I : Nat → Nat) (u ui p x : Nat) : Nat :=
  pcomp n w (mask w) (tP n w N T u p) (pcomp n w (mask w) x (tPI n w N T I ui p))

@[expose] noncomputable def cjProd (n w N : Nat) (T I : Nat → Nat) (u ui x : Nat) :
    List Nat → Nat :=
  List.rec (motive := fun _ => Nat) (pidn n w)
    (fun p _ ih => pcomp n w (mask w) (cjP n w N T I u ui p x) ih)

@[expose] noncomputable def b2K (n w ng NQ : Nat) (G Q B : Nat → Nat) (u y : Nat) : Bool :=
  (allN 16 fun m => (inPts n w NQ Q (B m) && eq22 n w (mask w) (B m) y y (B m)) ||
    exN NQ fun q => eq22 n w (mask w) (Q q) y y (Q q) &&
      eq22 n w (mask w) (Q q) y (B m) (pidn n w)) &&
  (allN NQ fun q => !eq22 n w (mask w) (Q q) y y (Q q) ||
    (inPts n w 16 B (Q q) && inPts n w 16 B (pcomp n w (mask w) (Q q) y))) &&
  (allN 16 fun m => isIdK n w (pcomp n w (mask w) (B m) (B m)) &&
    allN 16 fun m' => eq22 n w (mask w) (B m) (B m') (B m') (B m)) &&
  (allN 16 fun m => (allN ng fun k => exN 16 fun m' => eq22 n w (mask w) (G k) (B m) (B m') (G k)) &&
    exN 16 fun m' => eq22 n w (mask w) u (B m) (B m') u)

@[expose] noncomputable def outX (n w N : Nat) (T I B BG : Nat → Nat) (u ui x : Nat)
    (aw : List (List Nat)) (bw : List Nat) : Bool :=
  (inPts n w 16 B x &&
    allN 4 fun k => eqP n w (BG k) (cjProd n w N T I u ui x (aw.getD k []))) ||
  (strictB (cjP n w N T I u ui (bw.getD 0 0) x) fun c => !eq22 n w (mask w) c x x c) &&
    Nat.beq (cntN (N + N) fun p => strictB (tP n w N T u p) fun g =>
      eq22 n w (mask w) g x x g) 16 &&
    eq22 n w (mask w) (B (bw.getD 1 0)) x x (B (bw.getD 1 0)) &&
    Nat.blt (bw.getD 0 0) N && !inPts n w N T (B (bw.getD 1 0))

@[expose] noncomputable def outK (n w N : Nat) (T I B BG : Nat → Nat) (u ui : Nat)
    (aw : List (List (List Nat))) (bw : List (List Nat)) : Bool :=
  allN N fun i => strictB (pcomp n w (mask w) (T i) u) fun x =>
    !isInvK n w x || outX n w N T I B BG u ui x (aw.getD i []) (bw.getD i [])

end CFSG.KC.A45Cls

end
