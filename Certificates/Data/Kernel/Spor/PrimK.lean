module

public import Certificates.Data.Kernel.Spor.PChain

public section

namespace CFSG.KS.PR

open CFSG.KC.Enum CFSG.KS CFSG.KS.PEnum CFSG.KS.PC

@[expose] noncomputable def subPtK (k : Nat) (LBL REP : Nat → Nat) (SPTS SPOS : Nat → Nat → Nat)
    (SCNT : Nat → Nat) (z : Nat) : Bool :=
  strictB (r32 LBL z) fun l => bAnd(Nat.blt l k, bAnd(Nat.ble (r32 REP l) z,
    strictB (r32 (SPOS l) z) fun q => bAnd(Nat.blt q (SCNT l), Nat.beq (r32 (SPTS l) q) z)))

@[expose] noncomputable def subRepK (n k cnt0 : Nat) (LBL REP PTS0 POS0 : Nat → Nat) (l : Nat) :
    Bool :=
  strictB (r32 REP l) fun r => bAnd(Nat.blt r n, bAnd(Nat.beq (r32 LBL r) l,
    bAnd(Nat.blt (r32 POS0 r) cnt0, bAnd(Nat.beq (r32 PTS0 (r32 POS0 r)) r,
    bIf(Nat.blt (Nat.succ l) k, Nat.blt r (r32 REP (Nat.succ l)), true)))))

@[expose] noncomputable def subLblK (LBL : Nat → Nat) (SPTS : Nat → Nat → Nat) (l q : Nat) : Bool :=
  Nat.beq (r32 LBL (r32 (SPTS l) q)) l

@[expose] noncomputable def imAtK (L : Nat → Nat → Nat) (PAR0 LAB0 POS0 REP IM : Nat → Nat)
    (n l x : Nat) : Bool :=
  Nat.beq (List.getD (walkK L PAR0 LAB0 (r32 POS0 (r32 REP l)) (List.cons x List.nil)) (nat_lit 0)
    (nat_lit 0)) (r32 IM (Nat.add (Nat.mul l n) x))

@[expose] noncomputable def bitK (x j : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight x j) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def derStepK (n k : Nat) (LBL IM : Nat → Nat) (D s : Nat) : Nat :=
  strictN (Nat.shiftRight s (nat_lit 16)) fun j => strictN (Nat.land s (nat_lit 65535)) fun w =>
    nIf(bAnd(Nat.blt j k, bAnd(Nat.blt w n, bAnd(bitK D j, bitK D (r32 LBL w)))),
      Nat.lor D (Nat.shiftLeft (nat_lit 1) (r32 LBL (r32 IM (Nat.add (Nat.mul j n) w)))), D)

@[expose] noncomputable def derK (n k : Nat) (LBL IM DS DOFF DLEN : Nat → Nat) (i : Nat) : Bool :=
  strictB (r32 DOFF i) fun o =>
    Nat.beq (Nat.rec (motive := fun _ => Nat)
        (Nat.lor (Nat.shiftLeft (nat_lit 1) (r32 LBL (nat_lit 0))) (Nat.shiftLeft (nat_lit 1) i))
        (fun t D => strictN D fun D' => derStepK n k LBL IM D' (r32 DS (Nat.add o t))) (r32 DLEN i))
      (Nat.sub (Nat.shiftLeft (nat_lit 1) k) (nat_lit 1))

end CFSG.KS.PR

end
