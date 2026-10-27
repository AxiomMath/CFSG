module

public import Certificates.Data.Kernel.GMS78RuSClo

public section

namespace CFSG.KC.GMS

open CFSG.KLie.CT CFSG.KC.Loop

@[expose] noncomputable def cDTest (DM pd ud : Nat) : Bool :=
  Nat.beq (fget DM (Nat.add (Nat.mul 8 pd) ud) 3) (fget DM (Nat.add (Nat.mul 8 ud) pd) 3)

@[expose] noncomputable def cCTest (RP RU uc pc : Nat) : Bool :=
  Nat.beq (Nat.xor pc (Nat.land (fget RP uc 11) 255)) (Nat.xor uc (Nat.land (fget RU pc 11) 255))

@[expose] noncomputable def sCentT (m : Nat → Nat → Nat) (u base : Nat) (L acc : List Nat) :
    List Nat :=
  List.rec (motive := fun _ => List Nat) acc
    (fun pc _ ih => (fun p => Bool.rec (motive := fun _ => List Nat) ih (List.cons p ih)
      (Nat.beq (m p u) (m u p))) (Nat.add pc base)) L

@[expose] noncomputable def sCentD (m : Nat → Nat → Nat) (DPR : List Nat) (DM u pd : Nat)
    (acc : List Nat) : List Nat :=
  (fun uc ud => Bool.rec (motive := fun _ => List Nat) acc
    ((fun L => (fun b => sCentT m u b L (sCentT m u (Nat.add b 256) L
        (sCentT m u (Nat.add b 512) L (sCentT m u (Nat.add b 768) L acc))))
      (Nat.mul 1024 pd))
      (sFilter 256 fun pc => cCTest (neGet 0 DPR pd) (neGet 0 DPR ud) uc pc))
    (cDTest DM pd ud))
  (Nat.land u 255) (Nat.land (Nat.shiftRight u 10) 7)

@[expose] noncomputable def sCent17 (m : Nat → Nat → Nat) (DPR : List Nat) (DM u : Nat) :
    List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun pd _ ih => sCentD m DPR DM u pd ih) [0, 1, 2, 3, 4, 5, 6, 7]

@[expose] noncomputable def sKeyL (m : Nat → Nat → Nat) (u : Nat) (C : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun p _ ih => strictN ih fun a =>
    (fun s => Nat.add a (Nat.add 1 (Nat.add
      (Nat.shiftLeft (Bool.rec (motive := fun _ => Nat) 0 1 (Nat.beq s u)) 14)
      (Nat.shiftLeft (Bool.rec (motive := fun _ => Nat) 0 1 (Nat.beq s 256)) 28)))) (m p p)) C

@[expose] noncomputable def czPack9 (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun x _ ih s => Nat.lor (Nat.shiftLeft x s) (ih (Nat.add s 9))) l 0

@[expose] noncomputable def sMulRow (LIN DM DO RG RD pc pt pd q : Nat) : Nat :=
  (fun qt qd => (fun dp => (fun dc dt => Nat.add (Nat.xor pc dc) (Nat.add
      (Nat.mul 256 (Nat.land (Nat.shiftRight (Nat.xor (Nat.xor (Nat.xor (Nat.xor pt
          (fget LIN (Nat.add (Nat.mul 8 pd) qt) 3)) dt) (fget RG dc 3))
        (fget DO (Nat.add (Nat.mul 8 pd) qd) 1)) 1) 3))
      (Nat.mul 1024 (fget DM (Nat.add (Nat.mul 8 pd) qd) 3))))
    (Nat.land dp 255) (Nat.shiftRight dp 8)) (fget RD (Nat.land q 255) 11))
  (Nat.mul 2 (Nat.land (Nat.shiftRight q 8) 3)) (Nat.land (Nat.shiftRight q 10) 7)

@[expose] noncomputable def sRowP (GT : List (List Nat)) (DPR : List Nat) (LIN DM DO IDX : Nat)
    (C : List Nat) (p : Nat) : Nat :=
  (fun pc pt pd => strictN (sGamRow GT pc) fun RG => strictN (neGet 0 DPR pd) fun RD =>
      czPack9 (List.rec (motive := fun _ => List Nat) []
        (fun q _ ih => List.cons (fget IDX (sMulRow LIN DM DO RG RD pc pt pd q) 9) ih) C))
    (Nat.land p 255) (Nat.mul 2 (Nat.land (Nat.shiftRight p 8) 3)) (Nat.land (Nat.shiftRight p 10) 7)

@[expose] noncomputable def sRows (GT : List (List Nat)) (DPR : List Nat) (LIN DM DO IDX : Nat)
    (C : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun p _ ih => List.cons (sRowP GT DPR LIN DM DO IDX C p) ih) C

@[expose] noncomputable def sCols (R : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun i _ ih => List.cons (czPack9 (List.rec (motive := fun _ => List Nat) []
      (fun r _ ih2 => List.cons (fget r i 9) ih2) R)) ih) (List.range' 0 256)

@[expose] noncomputable def sZxT (R T : List Nat) (Rt : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun i _ ih => strictN ih fun a =>
    (fun Ri Ti => Nat.add a (Bool.rec (motive := fun _ => Nat) 0 1
      (allN (nat_lit 256) fun j => (fun pq qp => orB (Nat.beq pq qp)
          (Nat.beq pq (fget Rt (Nat.sub qp 1) 9))) (fget Ri j 9) (fget Ti j 9))))
      (neGet 0 R i) (neGet 0 T i)) (List.range' 0 256)

@[expose] noncomputable def sZxR (GT : List (List Nat)) (DPR : List Nat) (LIN DM DO : Nat)
    (C : List Nat) (u z : Nat) : Bool :=
  (fun IDX => (fun R => andB (neAllL (fun r => allN (nat_lit 256) fun j =>
        notB (Nat.beq (fget r j 9) 0)) R)
      ((fun T => Nat.beq (Nat.add (sZxT R T (neGet 0 R (Nat.sub (fget IDX u 9) 1)))
          (Nat.shiftLeft (sZxT R T (neGet 0 R (Nat.sub (fget IDX 256 9) 1))) 9)) z)
        (sCols R)))
    (sRows GT DPR LIN DM DO IDX C))
  (sIdx C)

@[expose] noncomputable def kAll17 (GT : List (List Nat)) (DPR : List Nat) (LIN DM DO u k : Nat) :
    Bool :=
  neStrictB u fun u => neStrictB k fun k =>
  (fun m => (fun C => andB (Nat.beq (sKeyL m u C) (kKeyPart k))
      (Bool.rec (motive := fun _ => Bool) (Nat.beq (Nat.shiftRight k 42) 0)
        (andB (Nat.beq (neLen C) 256) (sZxR GT DPR LIN DM DO C u (Nat.shiftRight k 42)))
        (kNeedZ u k)))
    (sCent17 m DPR DM u))
  (mul17K GT DPR LIN DM DO)

end CFSG.KC.GMS

end
