module

public import Certificates.Data.Kernel.Misc.PermClos
public import Certificates.Data.Kernel.Misc.PermM22

public section

namespace CFSG.KC.Co1Nine

open CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] noncomputable def letN (y : Nat) (k : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def byteK (k i : Nat) : Nat :=
  Nat.land (Nat.shiftRight k (Nat.mul (nat_lit 8) i)) (nat_lit 255)

@[expose] noncomputable def bitN (v i : Nat) : Nat := Nat.land (Nat.shiftRight v i) (nat_lit 1)

@[expose] noncomputable def capK (k v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.xor acc (Nat.mul (bitN v i) (byteK k i))) (nat_lit 8)

@[expose] noncomputable def mulC (a b : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (capK a (byteK b i)) (Nat.mul (nat_lit 8) i)))
    (nat_lit 8)

@[expose] noncomputable def idK : Nat := nat_lit 9241421688590303745

@[expose] noncomputable def baseF : Nat := nat_lit 2052

@[expose] noncomputable def stepF (g f : Nat) : Nat :=
  letN (capK g (Nat.shiftRight f (nat_lit 8))) fun p =>
    letN (capK g (Nat.land f (nat_lit 255))) fun q => letN (Nat.xor q p) fun r =>
      Nat.add (Nat.mul p (nat_lit 256)) (Bool.rec (motive := fun _ => Nat) r q (Nat.blt q r))

@[expose] noncomputable def actF (f g : Nat) : Nat := stepF g f

@[expose] def MCols : List (List Nat) :=
  [[33, 8, 63, 45, 74, 222, 9, 65], [159, 231, 96, 40, 41, 105, 234, 153],
    [9, 97, 105, 73, 28, 185, 250, 103], [126, 222, 174, 219, 131, 55, 95, 30],
    [82, 159, 179, 74, 67, 64, 2, 192], [126, 222, 174, 219, 131, 55, 95, 30],
    [231, 6, 24, 237, 112, 80, 224, 96], [250, 130, 236, 185, 190, 230, 56, 16]]

@[expose] def UCols : List (List Nat) :=
  [[1, 2, 4, 8, 20, 32, 65, 128], [36, 20, 4, 8, 6, 5, 115, 128],
    [52, 20, 4, 8, 6, 3, 117, 128], [1, 2, 12, 8, 16, 32, 72, 204]]

@[expose] noncomputable def MKL : List Nat :=
  [4686521297423763489, 11090792657845282719, 7492504461226107145, 2188528983391264382,
    13835691662995857234, 2188528983391264382, 6980667868368602855, 1168937810140103418]

@[expose] noncomputable def UKL : List Nat :=
  [9241703180746883585, 9255747182638928932, 9256307933569094708, 14720050635287036417]

@[expose] noncomputable def MG (l : Nat) : Nat := CFSG.KC.Misc.M22.nthL MKL l

@[expose] noncomputable def UG (j : Nat) : Nat := CFSG.KC.Misc.M22.nthL UKL j

@[expose] noncomputable def fixAt (E : Nat → Nat) (k : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) (allN (nat_lit 4) fun j => Nat.beq (stepF (UG j) (E k)) (E k))
    (fun _ _ => anyN (nat_lit 4) fun j => notB (Nat.beq (stepF (UG j) (E k)) (E k))) k

end CFSG.KC.Co1Nine

end
