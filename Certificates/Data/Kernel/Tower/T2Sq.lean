module

public import Certificates.Data.Kernel.Tower.Search

public section

namespace Certificates.KernelTower

@[expose] noncomputable def isG (mul : Nat → Nat → Nat) (GS FT h : Nat) : Bool :=
  Nat.beq (l16 FT h) h &&
    allB 4 fun i => Nat.beq (mul (l16 FT (l16 FT (l16 GS i))) h) (mul h (l16 GS i))

@[expose] noncomputable def ninv2 (mul : Nat → Nat → Nat) (HL FT g : Nat) : Nat :=
  Nat.add (cntB 128 fun j => !Nat.beq (hL HL j) 0 && Nat.beq (mul (hL HL j) (hL HL j)) 0)
    (cntB 128 fun j => Nat.beq (mul (mul (hL HL j) (l16 FT (hL HL j))) g) 0)

@[expose] noncomputable def gDeep (mul : Nat → Nat → Nat) (HL FT GL DP k : Nat) : Bool :=
  Nat.beq (l16 GL k) 65535 || Nat.beq (bit DP k) 1 || !Nat.beq (ninv2 mul HL FT (l16 GL k)) 87

@[expose] noncomputable def t2At (mul : Nat → Nat → Nat) (GS HL GL DP FT a : Nat) : Bool :=
  allB 128 (fun j => !isG mul GS FT (hL HL j) ||
      Nat.beq (hL HL j) (l16 GL (Nat.mul 2 a)) ||
      Nat.beq (hL HL j) (l16 GL (Nat.succ (Nat.mul 2 a)))) &&
    gDeep mul HL FT GL DP (Nat.mul 2 a) && gDeep mul HL FT GL DP (Nat.succ (Nat.mul 2 a))

end Certificates.KernelTower
