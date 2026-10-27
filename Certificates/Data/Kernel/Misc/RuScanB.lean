module

public import Certificates.Data.Kernel.Misc.RuScan

public section

namespace CFSG.KC.Misc.RuScan

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.RuInv

@[expose] noncomputable def witB (r : Nat) : Bool :=
  strictB (Nat.land r (nat_lit 3)) (fun c =>
    bIf(Nat.beq c (nat_lit 0), Nat.blt (fld(r, nat_lit 2, nat_lit 4095)) (nat_lit 4060),
    bIf(Nat.beq c (nat_lit 1),
      bAnd(Nat.blt (fld(r, nat_lit 7, nat_lit 4095)) (nat_lit 4060),
        Nat.blt (fld(r, nat_lit 19, nat_lit 4095)) (nat_lit 4060)),
      true)))

@[expose] noncomputable def bndK (W : Nat → Nat) (lo cnt : Nat) : Bool :=
  allN cnt (fun d => witB (W (Nat.add lo d)))

@[expose] noncomputable def kbndK (K : Nat → Nat) (lo cnt : Nat) : Bool :=
  allN cnt (fun d => Nat.blt (K (Nat.add lo d)) (nat_lit 4060))

@[expose] noncomputable def cjF (H HI : Nat) (f : Nat → Nat) (x : Nat) : Nat :=
  apP H (f (apP HI x))

@[expose] noncomputable def commP (f : Nat → Nat) (G : Nat) : Bool :=
  allN (nat_lit 4060) (fun x => Nat.beq (f (apP G x)) (apP G (f x)))

@[expose] noncomputable def eqF (f g : Nat → Nat) : Bool :=
  allN (nat_lit 4060) (fun x => Nat.beq (f x) (g x))

@[expose] noncomputable def p3K (H T : Nat) (Ls : Nat → Nat) (k : Nat) : Bool :=
  strictB (invP H) (fun HI =>
    bAnd(allN k (fun l => bAnd(commP (cjF H HI (apP T)) (Ls l),
        commP (cjF H HI (cjF H HI (apP T))) (Ls l))),
    bAnd(eqF (cjF H HI (cjF H HI (cjF H HI (apP T)))) (apP T),
    bAnd(bIf(eqF (cjF H HI (apP T)) (apP T), false, true),
      bIf(eqF (cjF H HI (cjF H HI (apP T))) (apP T), false, true)))))

end CFSG.KC.Misc.RuScan

end
