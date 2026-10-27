module

public import Certificates.Data.Kernel.RouteP.Geom
public import Certificates.Data.Kernel.PopF

public section

namespace CFSG.KC.RouteP

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.MonsterConv.Perm CFSG.KC.PopF

@[expose] noncomputable def sepS (k : Nat) : Nat :=
  nIf(Nat.blt k (nat_lit 19), (fun p => mk3 p p p) (idPlane (nat_lit 524288) k),
    nIf(Nat.beq k (nat_lit 19), mk3 full (nat_lit 0) (nat_lit 0), mk3 (nat_lit 0) full (nat_lit 0)))

@[expose] noncomputable def eqS (a b : Nat) : Nat := Nat.xor (ones (nat_lit 1572864)) (Nat.xor a b)

@[expose] noncomputable def fixR (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (z : Int) (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) ptsS
    (fun k ih => strictN ih (fun t => Nat.land t (eqS (sepS k) (imgS NW KA KB z (sepS k))))) n

@[expose] noncomputable def fixS (NW : Nat → Nat → Nat) (KA KB : Nat → Nat) (z : Int) : Nat :=
  fixR NW KA KB z (nat_lit 21)

@[expose] noncomputable def ptCount (s : Nat) : Nat := pcF (nat_lit 21) (Nat.land s ptsS)

@[expose] noncomputable def qcentCore (F G0 T Oq : Nat) (closed : Bool) : Bool :=
  andB closed
    (andB (Nat.beq (ptCount (Nat.land F G0)) (nat_lit 3511))
      (andB (Nat.beq (ptCount (Nat.land F T)) (nat_lit 695))
        (andB (Nat.beq (ptCount Oq) (nat_lit 693))
          (andB (Nat.beq (Nat.land Oq (single (nat_lit 99705))) (nat_lit 0))
            (letB (Nat.land (Nat.land T G0) F) fun X =>
              Nat.beq (Nat.land X (Nat.lor Oq (single (nat_lit 99705)))) X)))))

@[expose] noncomputable def qcentSetOK (NWP : Nat → Nat → Nat) (KAP KBP : Nat → Nat)
    (NWO : Nat → Nat → Nat) (KAO KBO : Nat → Nat) (NWQ : Nat → Nat → Nat) (KAQ KBQ : Nat → Nat)
    (zg qg : List Int) : Bool :=
  letB (closeS NWP KAP KBP zg (nat_lit 33) (single (nat_lit 1479))) fun G0 =>
  letB (fixS NWO KAO KBO 48) fun F =>
  letB (imgS NWO KAO KBO (-10) G0) fun T =>
  letB (closeS NWQ KAQ KBQ qg (nat_lit 5) (single (nat_lit 749820))) fun Oq =>
  qcentCore F G0 T Oq (closedS NWQ KAQ KBQ qg Oq)

end CFSG.KC.RouteP

end
