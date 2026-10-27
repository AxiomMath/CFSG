module

public import Certificates.Data.Kernel.Hall82K.Affine
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HexaStabData

public section

namespace CFSG.KC.Hall82K

open CFSG.ComponentClassification.AS81.Hexa

@[expose] def kMaskK : Nat := 9385823236096332062

@[expose] def inKK (v : Nat) : Bool := Nat.blt 0 (Nat.land kMaskK (Nat.shiftLeft 1 v))

@[expose] noncomputable def c5LvlK (i P : Nat) : Bool :=
  allN (fun d => band
      (bor (Bool.rec (motive := fun _ => Bool) true false (inKK (Nat.lor (Nat.shiftLeft 1 i) d)))
        (inKK (apL P (Nat.lor (Nat.shiftLeft 1 i) d))))
      (bor (Bool.rec (motive := fun _ => Bool) true false
          (Nat.beq (Nat.lor (Nat.shiftLeft 1 i) d) 5))
        (Nat.beq (apL P 5) 5)))
    (Nat.shiftLeft 1 i)

@[expose] noncomputable def c5LeafK (L : List Nat) (P : Nat) : Bool :=
  bor (Bool.rec (motive := fun _ => Bool) true false
      (allN (fun v => bor (Nat.beq v 0) (Bool.rec (motive := fun _ => Bool) true false
        (Nat.beq (apL P v) 0))) 64))
    (memL P L)

@[expose] noncomputable def c5SrchK (L : List Nat) (n : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (c5LeafK L)
    (fun n ih P => forBitsK (fun x =>
        bor (Bool.rec (motive := fun _ => Bool) true false
            (c5LvlK (Nat.sub 5 n) (Nat.lor P (Nat.shiftLeft x (Nat.mul 6 (Nat.sub 5 n))))))
          (ih (Nat.lor P (Nat.shiftLeft x (Nat.mul 6 (Nat.sub 5 n))))))
      64 kMaskK) n

@[expose] noncomputable def allLL (p : List Nat → Bool) (A : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun h _ ih => band (p h) ih) A

@[expose] noncomputable def anyLL (p : List Nat → Bool) (A : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun h _ ih => bor (p h) ih) A

@[expose] noncomputable def ovalOkK (f : Nat) : Bool :=
  allLL (fun L => anyLL (fun L' => allL (fun x => memL (apL f x) L') L) hexaOval) hexaOval

end CFSG.KC.Hall82K
