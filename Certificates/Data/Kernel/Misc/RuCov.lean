module

public import Certificates.Data.Kernel.Misc.RuScan

public section

namespace CFSG.KC.Misc.RuCov

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.RuInv CFSG.KC.Misc.RuScan

@[expose] noncomputable def conjOK (ss cs : List Nat) (R : Nat) : Bool :=
  allN (nat_lit 4) (fun b => Nat.beq (yAp cs (yAp ss b)) (apP R (yAp cs b)))

@[expose] noncomputable def recK (ss : List Nat) (T : Nat) (K3 : List Nat → Nat → Bool)
    (r : Nat) : Bool :=
  strictB (Nat.land r (nat_lit 3)) (fun k =>
    bIf(Nat.beq k (nat_lit 0),
      strictB (fld(r, nat_lit 2, nat_lit 4095)) (fun x =>
        bAnd(Nat.blt x (nat_lit 4060), bIf(Nat.beq (yAp ss (yAp ss x)) x, false, true))),
    bIf(Nat.beq k (nat_lit 1), allN (nat_lit 4) (fun b => Nat.beq (yAp ss b) b),
    bIf(Nat.beq k (nat_lit 2), allN (nat_lit 4) (fun b => Nat.beq (yAp ss b) (apP T b)),
      K3 ss r))))

@[expose] noncomputable def k3C (TR : Nat → Nat) (o0 o1 o2 n0 n1 n2 : Nat) (HR : Nat → Nat)
    (nR : Nat) (ss : List Nat) (r : Nat) : Bool :=
  strictB (fld(r, nat_lit 2, nat_lit 7)) (fun ρ =>
  strictB (fld(r, nat_lit 5, nat_lit 2047)) (fun a0 =>
  strictB (fld(r, nat_lit 16, nat_lit 63)) (fun a1 =>
  strictB (fld(r, nat_lit 22, nat_lit 1)) (fun a2 =>
    bAnd(Nat.blt ρ nR, bAnd(Nat.blt a0 n0, bAnd(Nat.blt a1 n1, bAnd(Nat.blt a2 n2,
      strictB (TR (Nat.add o0 a0)) (fun u0 =>
      strictB (TR (Nat.add o1 a1)) (fun u1 =>
      strictB (TR (Nat.add o2 a2)) (fun u2 =>
        conjOK ss [u0, u1, u2] (HR ρ))))))))))))

@[expose] noncomputable def k3L (TR : Nat → Nat) (o0 o1 n0 n1 : Nat) (HR : Nat → Nat)
    (nR : Nat) (ss : List Nat) (r : Nat) : Bool :=
  strictB (fld(r, nat_lit 2, nat_lit 7)) (fun ρ =>
  strictB (fld(r, nat_lit 5, nat_lit 2047)) (fun a0 =>
  strictB (fld(r, nat_lit 16, nat_lit 63)) (fun a1 =>
    bAnd(Nat.blt ρ nR, bAnd(Nat.blt a0 n0, bAnd(Nat.blt a1 n1,
      strictB (TR (Nat.add o0 a0)) (fun u0 =>
      strictB (TR (Nat.add o1 a1)) (fun u1 =>
        conjOK ss [u0, u1] (HR ρ)))))))))

@[expose] noncomputable def chkCov (LR TR W : Nat → Nat) (T : Nat) (K3 : List Nat → Nat → Bool)
    (lo cnt : Nat) : Bool :=
  strictB (roff (nat_lit 4060) (nat_lit 48720) (LR 0)) (fun o0 =>
  strictB (roff (nat_lit 4060) (nat_lit 48720) (LR 1)) (fun o1 =>
  strictB (rcnt (LR 1)) (fun c1 =>
  allN cnt (fun d => strictB (Nat.add lo d) (fun i =>
    strictB (TR (Nat.add o0 (Nat.div i c1))) (fun t0 =>
    strictB (TR (Nat.add o1 (Nat.mod i c1))) (fun t1 =>
      recK [t0, t1] T K3 (W i))))))))

end CFSG.KC.Misc.RuCov

end
