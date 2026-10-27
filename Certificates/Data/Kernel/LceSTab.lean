module

public import CFSG.Certificates.Kernel.Common.LceS
public import CFSG.Certificates.Kernel.Common.Bind

public section

namespace CFSG.Certificates.LCE

open CFSG.KC CFSG.KC.LceS

@[expose] noncomputable def wtPer (WT : Nat → Nat) (m : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun h ih => andB
    (Nat.rec (motive := fun _ => Bool) true (fun l ih2 => andB
      ((fun k => Nat.beq (WT k) (WT (Nat.mod k m))) (Nat.add (Nat.shiftLeft h (nat_lit 8)) l)) ih2)
      (nat_lit 256)) ih) (nat_lit 256)

@[expose] noncomputable def relsNorm (RT : Nat → Nat) (nR : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun r ih => andB
    (Nat.blt (wWord (RT r)) (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 8) (wLen (RT r))))) ih) nR

@[expose] noncomputable def lceOk (blk WT RT ST LVs : Nat → Nat)
    (INV INV8 L nC nCl mLV a m Hs nR nS nf : Nat) (Cs CCs : List Nat) (S0 S1 X0 X1 : Nat) : Bool :=
  andB (invOK INV INV8 L)
  (andB (wordsOK WT RT ST INV INV8 m Hs)
  (andB (CFSG.KC.Bind.hintsOK WT m nR nS Hs)
  (andB (aliveOK LVs mLV nCl a)
  (andB (Nat.beq nC nCl)
  (andB (Nat.ble nC (nat_lit 1048576))
  (andB (Nat.blt nf (nat_lit 4294967296))
  (andB (Nat.blt (nat_lit 0) m)
  (andB (wtPer WT m)
  (andB (relsNorm RT nR)
  (andB (Nat.beq S0 (mkS (nat_lit 0) (nat_lit 1)))
  (andB (Nat.beq (runFacts blk WT INV nC L Cs S0) S1)
  (andB (Nat.beq S1 (mkS nf nC))
  (andB (Nat.beq X0 (nat_lit 1))
  (andB (Nat.beq (runCover blk LVs nf L CCs X0) X1)
    (Nat.beq X1 (Nat.succ nC))))))))))))))))

end CFSG.Certificates.LCE

end
