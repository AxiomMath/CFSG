module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.OrbLab

open CFSG.KC.Enum

@[expose] noncomputable def olPt (n k : Nat) (f : Nat → Nat → Nat) (G PS blk Hd PR GN DP : Nat → Nat)
    (y : Nat) : Bool :=
  strictB (PS y) fun s => bAnd(Nat.blt s n, bAnd(Nat.beq (G s) y,
    bAnd(Nat.blt (G y) n, bAnd(Nat.beq (PS (G y)) y,
    bAnd(allN k (fun j => strictB (f j y) fun z => bAnd(Nat.blt z n, Nat.beq (blk (PS z)) (blk s))),
      bIf(Nat.beq (DP y) (nat_lit 0), Nat.beq y (Hd (blk s)),
        strictB (PR y) fun q => bAnd(Nat.blt q n, bAnd(Nat.blt (GN y) k,
          bAnd(Nat.beq (DP y) (Nat.succ (DP q)), Nat.beq (f (GN y) q) y)))))))))

@[expose] noncomputable def olOK (n k : Nat) (f : Nat → Nat → Nat) (G PS blk : Nat → Nat) (nt : Nat)
    (Hd PR GN DP : Nat → Nat) : Bool :=
  bAnd(allN n (olPt n k f G PS blk Hd PR GN DP),
    allN nt fun t => bAnd(Nat.blt (Hd t) n, Nat.beq (blk (PS (Hd t))) t))

end CFSG.KC.OrbLab

end
