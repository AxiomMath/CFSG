module

public import Certificates.Data.Kernel.HNFFibK
public import Certificates.Data.Kernel.F3152.Forms

public section

namespace CFSG.KC.HNFSub

open CFSG.KC.Ord CFSG.KC.HNF26720 CFSG.KC.HNF26729 CFSG.KC.HNFFib

@[expose] noncomputable def ln (v c : Nat) : Nat := bitsN v (Nat.mul 13 c) 13

@[expose] noncomputable def rowK (M k : Nat) : Nat := bitsN M (Nat.mul 1729 k) 1729

@[expose] noncomputable def mat4 (c0 c1 c2 c3 : Nat) : Nat :=
  Nat.add c0 (Nat.add (Nat.shiftLeft c1 1729) (Nat.add (Nat.shiftLeft c2 3458)
    (Nat.shiftLeft c3 5187)))

@[expose] noncomputable def getLs (l : List (List Nat)) : Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x _ ih i => Nat.rec (motive := fun _ => List Nat) x (fun j _ => ih j) i) l

@[expose] noncomputable def getSg (l : List (List (List Nat))) : Nat → List (List Nat) :=
  List.rec (motive := fun _ => Nat → List (List Nat)) (fun _ => [])
    (fun x _ ih i => Nat.rec (motive := fun _ => List (List Nat)) x (fun j _ => ih j) i) l

@[expose] noncomputable def dropN (n : Nat) : List Nat → List Nat :=
  Nat.rec (motive := fun _ => List Nat → List Nat) (fun l => l)
    (fun _ ih l => ih (List.rec (motive := fun _ => List Nat) [] (fun _ t _ => t) l)) n

@[expose] noncomputable def headN (d : Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) d (fun x _ _ => x) l

@[expose] noncomputable def atS (v : Nat) (S : List Nat) (e0 e1 e2 e3 : Nat) : Bool :=
  andB (Nat.beq (ln v (getN 0 S 0)) e0) (andB (Nat.beq (ln v (getN 0 S 1)) e1)
    (andB (Nat.beq (ln v (getN 0 S 2)) e2) (Nat.beq (ln v (getN 0 S 3)) e3)))

@[expose] noncomputable def img4 (vec : Nat → Nat → Nat) (P G : Nat) (k : Nat → Bool) : Bool :=
  strictB (vec (rowK P 0) G) fun c0 => strictB (vec (rowK P 1) G) fun c1 =>
  strictB (vec (rowK P 2) G) fun c2 => strictB (vec (rowK P 3) G) fun c3 =>
  strictB (mat4 c0 c1 c2 c3) k

@[expose] noncomputable def witOK (vec : Nat → Nat → Nat) (vldV : Nat → Bool) (C : Nat)
    (cols : List (List Nat)) : List Nat → Nat → (Nat → Bool) → Bool :=
  List.rec (motive := fun _ => Nat → (Nat → Bool) → Bool) (fun l k => k l)
    (fun x _ ih l k => andB (vldV x) (strictB (vec x C) fun y =>
      andB (notB (Nat.beq y 0)) (andB (atS y (getLs cols l) 0 0 0 0)
        (strictB (Nat.succ l) fun l' => ih l' k))))

@[expose] noncomputable def child (vec : Nat → Nat → Nat) (G0 G1 P g : Nat) (k : Nat → Bool) : Bool :=
  Bool.rec (motive := fun _ => Bool) (img4 vec P (nIf(Nat.beq g 0, G0, G1)) k) (k P)
    (Nat.beq g 2)

@[expose] noncomputable def node (vec : Nat → Nat → Nat) (vldV : Nat → Bool) (G0 G1 : Nat)
    (cols : List (List Nat)) (P : Nat) (r : List Nat) (k : Nat → Bool) : Bool :=
  child vec G0 G1 P (bitsN (getN 0 r 0) 1 2) fun C =>
  andB (vldV (getN 0 r 1)) (andB (vldV (getN 0 r 2)) (andB (vldV (getN 0 r 3))
    (andB (vldV (getN 0 r 4)) (
  strictB (vec (getN 0 r 1) C) fun r0 => strictB (vec (getN 0 r 2) C) fun r1 =>
  strictB (vec (getN 0 r 3) C) fun r2 => strictB (vec (getN 0 r 4) C) fun r3 =>
  witOK vec vldV C cols (dropN 6 r) 0 fun j =>
  andB (atS r0 (getLs cols j) 1 0 0 0) (andB (atS r1 (getLs cols j) 0 1 0 0)
    (andB (atS r2 (getLs cols j) 0 0 1 0) (andB (atS r3 (getLs cols j) 0 0 0 1)
      (andB (Nat.beq (bitsN (Nat.add r0 (Nat.add (Nat.mul 7 r1) (Nat.add (Nat.mul 49 r2)
        (Nat.mul 343 r3)))) 65 130) (getN 0 r 5))
        (strictB (mat4 r0 r1 r2 r3) k)))))))))

@[expose] noncomputable def walk (vec : Nat → Nat → Nat) (vldV : Nat → Bool) (G0 G1 B : Nat)
    (cols : List (List Nat)) : List (List Nat) → List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun r _ ih st => node vec vldV G0 G1 cols (headN B (dropN (Nat.shiftRight (getN 0 r 0) 3) st))
      r fun R => ih (R :: dropN (Nat.shiftRight (getN 0 r 0) 3) st))

@[expose] noncomputable def base (r0 : List Nat) : Nat :=
  mat4 (getN 0 r0 0) (getN 0 r0 1) (getN 0 r0 2) (getN 0 r0 3)

@[expose] noncomputable def segOK (mul vec : Nat → Nat → Nat) (vldV : Nat → Bool)
    (A B Bi ONE : Nat) (w1 w2 : List Int) (r0 : List Nat) (cols : List (List Nat))
    (seg : List (List Nat)) : Bool :=
  strictB (wprod mul A B Bi ONE (invW w1)) fun g1i =>
  strictB (wprod mul A B Bi ONE (invW w2)) fun g2i =>
  walk vec vldV g1i g2i (base r0) cols seg []

@[expose] noncomputable def keysOf (recs : List (List Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun r _ ih => Bool.rec (motive := fun _ => List Nat) ih (getN 0 r 5 :: ih)
      (Nat.beq (Nat.land (getN 0 r 0) 1) 1)) recs

@[expose] noncomputable def allKeys (segs : List (List (List Nat))) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun s _ ih => keysOf s ++ ih) segs

@[expose] noncomputable def msortH (ks : List Nat) : List Nat :=
  (CFSG.KS.F3152.passK (nat_lit 131072) (nat_lit 17) (ks.map fun k => [k])).flatten

@[expose] noncomputable def distOK (N : Nat) (segs : List (List (List Nat))) : Bool :=
  andB (Nat.beq (allKeys segs).length N) (CFSG.KS.F3152.sortedK (msortH (allKeys segs)))

@[expose] noncomputable def addOne (L H ONE X : Nat) : Nat := redP 13 L H 5 9 (Nat.add X ONE)

@[expose] noncomputable def eMat (r0 S : List Nat) : Nat :=
  Nat.add (Nat.shiftLeft (getN 0 r0 0) (Nat.mul 1729 (getN 0 S 0)))
    (Nat.add (Nat.shiftLeft (getN 0 r0 1) (Nat.mul 1729 (getN 0 S 1)))
      (Nat.add (Nat.shiftLeft (getN 0 r0 2) (Nat.mul 1729 (getN 0 S 2)))
        (Nat.shiftLeft (getN 0 r0 3) (Nat.mul 1729 (getN 0 S 3)))))

@[expose] noncomputable def baseOK (mul vec : Nat → Nat → Nat) (vld vldV : Nat → Bool)
    (L H A B Bi ONE : Nat) (w : List Int) (r0 : List Nat) (S0 : List Nat) (X Y : Nat) : Bool :=
  andB (vldV (getN 0 r0 0)) (andB (vldV (getN 0 r0 1)) (andB (vldV (getN 0 r0 2))
    (andB (vldV (getN 0 r0 3)) (andB (vld X) (andB (vld Y)
  (andB (Nat.blt (getN 0 S0 0) (getN 0 S0 1)) (andB (Nat.blt (getN 0 S0 1) (getN 0 S0 2))
    (andB (Nat.blt (getN 0 S0 2) (getN 0 S0 3)) (andB (Nat.blt (getN 0 S0 3) 133)
  (andB (atS (getN 0 r0 0) S0 1 0 0 0) (andB (atS (getN 0 r0 1) S0 0 1 0 0)
    (andB (atS (getN 0 r0 2) S0 0 0 1 0) (andB (atS (getN 0 r0 3) S0 0 0 0 1) (
  strictB (addOne L H ONE A) fun a1 =>
  strictB (addOne L H ONE (wprod mul A B Bi ONE (w ++ 1 :: invW w))) fun b1 =>
  andB (Nat.beq (vec (getN 0 r0 0) a1) 0) (andB (Nat.beq (vec (getN 0 r0 1) a1) 0)
    (andB (Nat.beq (vec (getN 0 r0 2) a1) 0) (andB (Nat.beq (vec (getN 0 r0 3) a1) 0)
  (andB (Nat.beq (vec (getN 0 r0 0) b1) 0) (andB (Nat.beq (vec (getN 0 r0 1) b1) 0)
    (andB (Nat.beq (vec (getN 0 r0 2) b1) 0) (andB (Nat.beq (vec (getN 0 r0 3) b1) 0)
  (Nat.beq (redP 13 L H 5 9 (Nat.add (redP 13 L H 5 9 (Nat.add (mul a1 X) (mul b1 Y)))
    (eMat r0 S0))) ONE))))))))))))))))))))))

@[expose] noncomputable def stabOK (vec : Nat → Nat → Nat) (vldV : Nat → Bool) (R : Nat) :
    List (Nat × Nat) → List (List Nat) → Bool :=
  List.rec (motive := fun _ => List (List Nat) → Bool) (fun ts => Nat.beq ts.length 0)
    (fun p _ ih ts => List.rec (motive := fun _ => Bool) false (fun t ts' _ =>
      img4 vec R p.1 fun C =>
      andB (vldV (getN 0 t 0)) (andB (vldV (getN 0 t 1)) (andB (vldV (getN 0 t 2))
        (andB (vldV (getN 0 t 3)) (andB (Nat.beq (mat4 (vec (getN 0 t 0) C)
          (vec (getN 0 t 1) C) (vec (getN 0 t 2) C) (vec (getN 0 t 3) C)) R) (ih ts')))))) ts)

@[expose] noncomputable def fibU (mul vec : Nat → Nat → Nat) (vldV : Nat → Bool)
    (A B Bi ONE : Nat) (w1 w2 w : List Int) (r0 : List Nat) (us ts : List (List Nat))
    (u N : Nat) (t : List (Nat × Nat)) (ord : List Nat) : Bool :=
  andB (okWs us) (
  strictB (wprod mul A B Bi ONE w1) fun g1 =>
  strictB (wprod mul A B Bi ONE (invW w1)) fun g1i =>
  strictB (wprod mul A B Bi ONE w2) fun g2 =>
  strictB (wprod mul A B Bi ONE (invW w2)) fun g2i =>
  andB (Nat.beq (mul A g1) (mul g1 A)) (andB (Nat.beq (mul A g2) (mul g2 A)) (
  strictB (wprod mul A B Bi ONE (w ++ 1 :: invW w)) fun bi =>
  regs mul (ltr3 A g1 g1i g2 g2i) ONE us fun Lr =>
  andB (stabOK vec vldV (base r0) Lr ts) (andB (vldV u) (andB (Nat.beq ord.length N)
    (goT mul bi ONE Lr t [bi] fun l => incrV vec u bi l ord 0))))))

end CFSG.KC.HNFSub

end
