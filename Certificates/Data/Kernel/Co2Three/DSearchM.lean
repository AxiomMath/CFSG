module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.Co2Three

open CFSG.KC.Enum

@[expose] noncomputable def dsearchM (vm mm : Nat → Nat → Nat) (VG BS LK : Nat → Nat) (RF FF : Nat → Bool)
    (RS RY : Nat → Nat) (FX : Nat → Nat → Bool) (PR : Nat → Bool) (m : Nat → Nat) (PT PO TM TIM : Nat → Nat → Nat) :
    Nat → Nat → Nat → Nat → Nat
  | 0, _, A, _ => nIf(PR A, 1, 0)
  | fuel + 1, i, A, AI =>
    Bool.rec (motive := fun _ => Nat)
      (foldN (m i) (fun k s => Nat.add s
        (nIf(bIf(FF i, FX i (vm (VG (PT i k)) A), true),
          strictN (mm (TM i k) A) fun A' => strictN (mm AI (TIM i k)) fun AI' =>
            dsearchM vm mm VG BS LK RF FF RS RY FX PR m PT PO TM TIM fuel (i + 1) A' AI', 0))) 0)
      (strictN (vm (vm (VG (BS (RS i))) A) (RY i)) fun u =>
        nIf(FX i u, strictN (PO i (LK (vm u AI))) fun k =>
          nIf(Nat.blt k (m i),
            strictN (mm (TM i k) A) fun A' => strictN (mm AI (TIM i k)) fun AI' =>
              dsearchM vm mm VG BS LK RF FF RS RY FX PR m PT PO TM TIM fuel (i + 1) A' AI', 0), 0))
      (RF i)

@[expose] noncomputable def dig3 (k t : Nat) : Nat := Nat.mod (Nat.div k (Nat.pow 3 t)) 3

@[expose] noncomputable def dotK (a b : Nat) : Nat :=
  Nat.mod (Nat.add (Nat.add (Nat.mul (dig3 a 0) (dig3 b 0)) (Nat.mul (dig3 a 1) (dig3 b 1)))
    (Nat.add (Nat.mul (dig3 a 2) (dig3 b 2)) (Nat.mul (dig3 a 3) (dig3 b 3)))) 3

@[expose] noncomputable def linD (C : Nat → Nat) (k r : Nat) : Nat :=
  Nat.mod (Nat.add (Nat.add (Nat.mul (dig3 k 0) (dig3 (C 0) r)) (Nat.mul (dig3 k 1) (dig3 (C 1) r)))
    (Nat.add (Nat.mul (dig3 k 2) (dig3 (C 2) r)) (Nat.mul (dig3 k 3) (dig3 (C 3) r)))) 3

@[expose] noncomputable def linK (C : Nat → Nat) (k : Nat) : Nat :=
  Nat.add (Nat.add (linD C k 0) (Nat.mul 3 (linD C k 1)))
    (Nat.add (Nat.mul 9 (linD C k 2)) (Nat.mul 27 (linD C k 3)))

end CFSG.KC.Co2Three

end
