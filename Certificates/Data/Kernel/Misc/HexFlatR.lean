module

public import Certificates.Data.Kernel.Misc.HexFlat

public section

namespace CFSG.KC.Misc.HexFlat

open CFSG.KS.Text (hexV)

@[expose] noncomputable def stepHexR (d n w N : Nat) (F : Nat → Nat) (ch : Char)
    (ih : Nat → Nat → Nat → Nat → Nat → Bool) (j e t v rest : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) false
      (Bool.rec (motive := fun _ => Bool)
        (ih j e (Nat.succ t) (Nat.add (Nat.mul v 16) (hexV (Char.toNat ch))) rest)
        (Bool.rec (motive := fun _ => Bool) false
          (Bool.rec (motive := fun _ => Bool)
            (ih j (Nat.succ e) 0 0 (Nat.shiftRight rest w))
            (Bool.rec (motive := fun _ => Bool) false
              (ih (Nat.succ j) 0 0 0 (F (Nat.succ j)))
              (Nat.beq (Nat.shiftRight rest w) 0))
            (Nat.beq (Nat.succ e) n))
          (Nat.beq (Nat.add (Nat.mul v 16) (hexV (Char.toNat ch)))
            (Nat.land rest (Nat.sub (Nat.shiftLeft 1 w) 1))))
        (Nat.beq (Nat.succ t) d))
      (Nat.blt (hexV (Char.toNat ch)) 16))
    true (Nat.beq j N)

@[expose] noncomputable def runHexR (d n w N : Nat) (F : Nat → Nat) (cs : List Char) :
    Nat → Nat → Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Nat → Bool)
    (fun j _ _ _ _ => Nat.beq j N) (fun ch _ ih => stepHexR d n w N F ch ih) cs

@[expose] noncomputable def hexFlatR (cs : List Char) (d n w N : Nat) (F : Nat → Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false
    (Bool.rec (motive := fun _ => Bool) false (runHexR d n w N F cs 0 0 0 0 (F 0)) (Nat.blt 0 n))
    (Nat.blt 0 d)

end CFSG.KC.Misc.HexFlat

end
