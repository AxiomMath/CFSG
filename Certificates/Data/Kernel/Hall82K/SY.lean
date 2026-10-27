module

public import Certificates.Data.Kernel.Hall82K.ML
public import Certificates.Data.Kernel.Hall82K.MR
public import Certificates.Data.Kernel.F4M3B

public section

namespace CFSG.KC.Hall82K

open CFSG.KC.Ord CFSG.KC.LQT CFSG.KC.F4M3B

@[expose] noncomputable def syE (E : Nat → Nat) (I i : Nat) : Nat := E (lane I 12 4095 i)

@[expose] def syT (T i j : Nat) : Nat := lane T 4 15 (Nat.add (Nat.mul 16 i) j)

@[expose] noncomputable def syBasicK (E : Nat → Nat) (I T : Nat) : Bool :=
  andB (Nat.beq (syE E I 0) idK)
    (P.allN 16 fun i => andB (Nat.blt (lane I 12 4095 i) 2160)
      (P.allN 16 fun j => andB (Nat.beq (compL (syE E I i) (syE E I j)) (syE E I (syT T i j)))
        (P.impB (Nat.beq (syE E I i) (syE E I j)) (Nat.beq i j))))

@[expose] def onesK : Nat := Nat.sub (Nat.pow 2 65536) 1

@[expose] noncomputable def clPair (T i j : Nat) : Nat :=
  Nat.lor (Nat.xor (pln i 16) onesK) (Nat.lor (Nat.xor (pln j 16) onesK) (pln (syT T i j) 16))

@[expose] noncomputable def clPl (T : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) onesK
    (fun k acc => Nat.land acc (clPair T (Nat.div k 16) (Nat.mod k 16))) 256

@[expose] noncomputable def xorPow (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun m _ ih => Nat.xor (Nat.shiftLeft 1 m) ih) L

@[expose] noncomputable def syClK (T : Nat) (L : List Nat) : Bool := Nat.beq (clPl T) (xorPow L)

@[expose] def inS (m i : Nat) : Bool := Nat.beq (bitN m i) 1

@[expose] noncomputable def fixSK (E : Nat → Nat) (I m : Nat) : Nat :=
  cntK (fun v => P.allN 16 fun i => P.impB (inS m i) (Nat.beq (apL (syE E I i) v) v)) 64

@[expose] noncomputable def allZK (E : Nat → Nat) (I Z m : Nat) : Bool :=
  P.allN 16 fun i => P.impB (inS m i) (commK (syE E I i) Z)

@[expose] noncomputable def allSqK (E : Nat → Nat) (I m : Nat) : Bool :=
  P.allN 16 fun i => P.impB (inS m i) (Nat.beq (compL (syE E I i) (syE E I i)) idK)

@[expose] noncomputable def syCondK (E : Nat → Nat) (I Z m : Nat) : Bool :=
  P.letB (cntK (inS m) 16) fun c => P.letB (fixSK E I m) fun F =>
    andB (Nat.ble (Nat.mul c F) 64)
      (andB (orB (allZK E I Z m) (Nat.ble (Nat.mul c F) 32))
        (orB (Nat.blt c 4)
          (orB (P.anyN 16 fun i => andB (inS m i) (andB (negK (Nat.beq i 0))
              (negK (Nat.beq (cntK (fun v => Nat.beq (apL (syE E I i) v) v) 64) F))))
            (andB (Nat.beq c 4) (andB (allZK E I Z m) (andB (allSqK E I m) (Nat.beq F 16)))))))

@[expose] noncomputable def syListK (E : Nat → Nat) (I Z : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun m _ ih => andB (syCondK E I Z m) ih) L

end CFSG.KC.Hall82K
