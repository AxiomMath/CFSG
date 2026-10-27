module

public import CFSG.Certificates.Kernel.Common.HOrb
public import Certificates.Data.Kernel.LceSTab

public section

namespace CFSG.Certificates.HO

open CFSG.KC CFSG.KC.LceS

@[expose] noncomputable def factsOk (blk WT RT ST : Nat → Nat) (INV INV8 L nC m Hs nR nS nf S0 S1 : Nat)
    (Cs : List Nat) : Bool :=
  andB (invOK INV INV8 L)
  (andB (wordsOK WT RT ST INV INV8 m Hs)
  (andB (CFSG.KC.Bind.hintsOK WT m nR nS Hs)
  (andB (Nat.blt (nat_lit 0) m)
  (andB (CFSG.Certificates.LCE.wtPer WT m)
  (andB (CFSG.Certificates.LCE.relsNorm RT nR)
  (andB (Nat.ble nC (nat_lit 1048576))
  (andB (Nat.blt nf (nat_lit 4294967296))
  (andB (Nat.beq S0 (mkS (nat_lit 0) (nat_lit 1)))
  (andB (Nat.beq S1 (mkS nf nC))
    (Nat.beq (runFacts blk WT INV nC L Cs S0) S1))))))))))

@[expose] noncomputable def lettersBelow (W n b : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun q acc => andB acc (Nat.blt (wLet W q) b)) n

@[expose] noncomputable def entOK (e b n : Nat) : Bool :=
  andB (Nat.blt (wWord e) (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 8) (wLen e))))
    (andB (Nat.ble (wLen e) n) (lettersBelow (wWord e) (wLen e) b))

end CFSG.Certificates.HO

end
