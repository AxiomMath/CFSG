module

public import Certificates.Data.Kernel.B433Alt.Struct

public section

namespace CFSG.KC.B4A

@[expose] def divsOf (F : List (Nat × Nat)) : List Nat :=
  F.foldr (fun pe acc => acc.flatMap fun d => (List.range (pe.2 + 1)).map fun k => d * pe.1 ^ k) [1]

@[expose] noncomputable def ssRot (m s R : Nat) : Nat :=
  Nat.land (Nat.lor (Nat.shiftLeft R s) (Nat.shiftRight R (Nat.sub m s))) (ones m)

@[expose] noncomputable def ssMod (w : Nat → Nat) (idx : List Nat) (m : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun R => R)
    (fun j _ ih R => sN (Nat.lor R (ssRot m (Nat.mod (w j) m) R)) ih) idx (nat_lit 1)

@[expose] noncomputable def ssChk (w : Nat → Nat) (idx : List Nat) (F : List (Nat × Nat)) (A : List Nat)
    (T m k : Nat) : Bool :=
  sB (ssMod w idx m) (fun R =>
    List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
      (fun d _ ih A' => List.rec (motive := fun _ => Bool) false
        (fun a A'' _ => andB
          (orB (notB (Nat.beq a k)) (orB (Nat.ble d (nat_lit 1)) (orB (Nat.ble T d)
            (Nat.beq (Nat.land (Nat.shiftRight R (Nat.mod (Nat.sub d (nat_lit 1)) m)) (nat_lit 1))
              (nat_lit 0)))))
          (ih A'')) A')
      (divsOf F) A)

end CFSG.KC.B4A

end
