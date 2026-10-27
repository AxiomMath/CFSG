module

public import Certificates.Data.Kernel.GMS78RuSCent
public import Certificates.Data.Kernel.GMS78RuCzJ

public section

namespace CFSG.KC.GMS

open CFSG.KLie.CT CFSG.KC.Loop

@[expose] noncomputable def gAnyL (p : Nat → Bool) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => orB (p a) ih) l

@[expose] noncomputable def gMap (f : Nat → Nat) (L : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun x _ ih => List.cons (f x) ih) L

@[expose] noncomputable def kGrpOne (m : Nat → Nat → Nat) (DPR : List Nat) (DM : Nat)
    (C R T : List Nat) (IDX z2 u k : Nat) : Bool :=
  neStrictB u fun u => neStrictB k fun k =>
  andB (czListEq (sCent17 m DPR DM u) C) (andB (kNeedZ u k)
    (andB (Nat.beq (sKeyL m u C) (kKeyPart k))
      (Nat.beq (Nat.add (sZxT R T (neGet 0 R (Nat.sub (fget IDX u 9) 1))) (Nat.shiftLeft z2 9))
        (Nat.shiftRight k 42))))

@[expose] noncomputable def kGrp17 (GT : List (List Nat)) (DPR : List Nat) (LIN DM DO u0 : Nat)
    (U K : List Nat) : Bool :=
  (fun m => (fun C => andB (Nat.beq (neLen C) 256) ((fun IDX => (fun R =>
      andB (neAllL (fun r => allN (nat_lit 256) fun j => notB (Nat.beq (fget r j 9) 0)) R)
        ((fun T => neStrictB (sZxT R T (neGet 0 R (Nat.sub (fget IDX 256 9) 1))) fun z2 =>
            sZipAll (kGrpOne m DPR DM C R T IDX z2) U K)
          (sCols R)))
      (sRows GT DPR LIN DM DO IDX C)) (sIdx C)))
    (sCent17 m DPR DM u0))
  (mul17K GT DPR LIN DM DO)

@[expose] noncomputable def kGrpAt (GT : List (List Nat)) (DPR : List Nat) (LIN DM DO : Nat)
    (I K P : List Nat) : Bool :=
  kGrp17 GT DPR LIN DM DO (neGet 0 I (neGet 0 P 0)) (gMap (neGet 0 I) P) (gMap (neGet 0 K) P)

@[expose] noncomputable def kAll17H (GT : List (List Nat)) (DPR : List Nat) (LIN DM DO : Nat)
    (I K : List Nat) (G : List (List Nat)) (n j : Nat) : Bool :=
  (fun u k => Bool.rec (motive := fun _ => Bool) (kAll17 GT DPR LIN DM DO u k)
      (anyN n fun g => gAnyL (fun p => Nat.beq p j) (neGet [] G g)) (kNeedZ u k))
    (neGet 0 I j) (neGet 0 K j)

end CFSG.KC.GMS

end
