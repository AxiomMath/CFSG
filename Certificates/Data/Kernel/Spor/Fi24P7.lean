module

public import Certificates.Data.Kernel.Spor.Fi24Orb

public section

namespace CFSG.KC.Fi24P7

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.Fi24FixK

@[expose] noncomputable def incStep (FL : Nat → Nat) (n m j : Nat) : Bool :=
  letB (FL j) (fun r => andB (Nat.blt r n)
    (orB (Nat.ble m (Nat.succ j)) (Nat.blt r (FL (Nat.succ j)))))

@[expose] noncomputable def wStep (TG : Nat → Nat → Nat) (FL P : Nat → Nat) (w : List Nat)
    (m j : Nat) : Bool :=
  letB (P j) (fun p => andB (Nat.blt p m) (Nat.beq (walk TG w (FL j)) (FL p)))

@[expose] noncomputable def tStep (PA PB PAR DEP : Nat → Nat) (m j0 j : Nat) : Bool :=
  orB (Nat.beq j j0) (letB (PAR j) (fun q => andB (Nat.blt q m) (andB (Nat.blt (DEP q) (DEP j))
    (orB (Nat.beq (PA q) j) (Nat.beq (PB q) j)))))

@[expose] noncomputable def qStep (Q QA P : Nat → Nat) (m1 M k : Nat) : Bool :=
  letB (QA k) (fun q => letB (Q k) (fun c => andB (Nat.blt q M)
    (Nat.beq (Q q) (Nat.add (Nat.mul m1 (P (Nat.div c m1))) (P (Nat.mod c m1))))))

@[expose] noncomputable def qIncStep (Q : Nat → Nat) (m1 M k : Nat) : Bool :=
  letB (Q k) (fun c => andB (Nat.blt c (Nat.mul m1 m1))
    (orB (Nat.ble M (Nat.succ k)) (Nat.blt c (Q (Nat.succ k)))))

end CFSG.KC.Fi24P7

end
