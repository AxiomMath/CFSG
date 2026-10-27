module

public import Certificates.Data.Kernel.U6.M22Cnt

public section

namespace CFSG.KC.U6

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KC.M1F2

@[expose] noncomputable def unkey (k : Nat) : Nat :=
  sumN (nat_lit 22) fun i =>
    Nat.shiftLeft (fget k (Nat.sub (nat_lit 21) i) (nat_lit 5)) (Nat.mul (nat_lit 5) i)

@[expose] noncomputable def PV : Nat := nat_lit 411273209911639352122403288448403354630599278738832159502269155329

@[expose] noncomputable def actK (t m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => strictN acc fun acc =>
      nIf(Nat.beq (fget m i (nat_lit 1)) (nat_lit 1), Nat.xor acc (fget PV (ap5 t i) (nat_lit 10)),
        acc))
    (nat_lit 22)

@[expose] noncomputable def inK (span : List Nat) (y : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun s _ ih => orB (Nat.beq s y) ih) span

@[expose] noncomputable def newGenK (span : List Nat) (y : Nat) : Bool :=
  andB (notB (inK span y)) (strictB (keyK y) fun ky =>
    List.rec (motive := fun _ => Bool) true
      (fun s _ ih => andB (Nat.ble ky (keyK (pc22 y s))) ih) span)

@[expose] noncomputable def mapComp (y : Nat) (span : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun s _ ih => pc22 y s :: ih) span

@[expose] noncomputable def filtFix (y : Nat) (fix : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun m _ ih => Bool.rec (motive := fun _ => List Nat) ih (m :: ih) (Nat.beq (actK y m) m)) fix

@[expose] noncomputable def filtComm (y : Nat) (ys : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun z _ ih => Bool.rec (motive := fun _ => List Nat) ih (z :: ih)
      (Nat.beq (pc22 y z) (pc22 z y))) ys

@[expose] noncomputable def nodeK (B : Nat) : Nat → List Nat → List Nat → List Nat → Bool :=
  Nat.rec (motive := fun _ => List Nat → List Nat → List Nat → Bool) (fun _ _ _ => false)
    (fun _ ih span fix rest =>
      andB (Nat.ble (Nat.mul (List.length span) (List.length fix)) B)
        (List.rec (motive := fun _ => Bool) true
          (fun y ys acc => andB (orB (notB (newGenK span y))
            (ih (List.append span (mapComp y span)) (filtFix y fix) (filtComm y ys))) acc) rest))

@[expose] noncomputable def fixMK (t : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) []
    (fun j acc => (fun m => Bool.rec (motive := fun _ => List Nat) acc (m :: acc)
      (Nat.beq (actK t m) m)) (Nat.sub (nat_lit 1023) j)) (nat_lit 1024)

@[expose] noncomputable def id22 : Nat := sumN (nat_lit 22) fun i => Nat.shiftLeft i (Nat.mul (nat_lit 5) i)

@[expose] noncomputable def rootK (B k : Nat) (L : List Nat) : Bool :=
  strictB (unkey k) fun T =>
    nodeK B (nat_lit 8) [id22, T] (fixMK T)
      (List.rec (motive := fun _ => List Nat) [] (fun x _ ih => unkey x :: ih) L)

end CFSG.KC.U6

end
