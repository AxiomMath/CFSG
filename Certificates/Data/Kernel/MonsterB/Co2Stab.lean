module

public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KS.Co2Stab

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def labP (p : Nat) : Nat :=
  nIf(Nat.blt p (nat_lit 1), nat_lit 0, nIf(Nat.blt p (nat_lit 892), nat_lit 1, nat_lit 2))

@[expose] noncomputable def at12 (P p : Nat) : Nat := pg (nat_lit 12) (nat_lit 4095) P p

@[expose] noncomputable def stabK (PS : Nat → Nat) (OP OPI WP WG WD : Nat) : Bool :=
  bAnd(permOK (nat_lit 2300) (nat_lit 12) (nat_lit 4095) (nat_lit 27600) OP OPI,
  bAnd(permOK (nat_lit 2300) (nat_lit 12) (nat_lit 4095) (nat_lit 27600) OPI OP,
  bAnd(allN (nat_lit 2299) (fun p => bIf(Nat.beq p (nat_lit 0), true, bIf(Nat.beq p (nat_lit 891),
    true, Nat.blt (at12 OP p) (at12 OP (Nat.succ p))))),
  bAnd(allN (nat_lit 2300) (fun z => strictB (labP (at12 OPI z)) (fun t =>
    allN (nat_lit 18) (fun j => Nat.beq (labP (at12 OPI (at12 (PS (Nat.add j (nat_lit 2))) z))) t))),
  allN (nat_lit 2300) (fun z => strictB (at12 OPI z) (fun p =>
    bIf(Nat.beq p (nat_lit 0), Nat.beq (at12 WD z) (nat_lit 0),
    bIf(Nat.beq p (nat_lit 1), Nat.beq (at12 WD z) (nat_lit 0),
    bIf(Nat.beq p (nat_lit 892), Nat.beq (at12 WD z) (nat_lit 0),
      strictB (at12 WP z) (fun y => strictB (at12 WG z) (fun g =>
        bAnd(Nat.blt y (nat_lit 2300), bAnd(Nat.blt g (nat_lit 18),
        bAnd(Nat.beq (at12 (PS (Nat.add g (nat_lit 2))) y) z,
          Nat.beq (Nat.succ (at12 WD y)) (at12 WD z)))))))))))))))

end CFSG.KS.Co2Stab

end
