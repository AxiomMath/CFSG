module

public import Certificates.Data.Kernel.L34W.Tab42
public import Certificates.Data.Kernel.L34K
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsFieldCertInputs

public section

namespace CFSG.KC.L34Field

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34W
open CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.KLie.CT (andB orB notB)

@[expose] noncomputable def wK (G : Nat → Nat) (w : List Nat) : Nat :=
  pword (gS G) w (pidn (nat_lit 42) (nat_lit 6))

@[expose] noncomputable def nnK (TT TG : Nat → Nat) (r y yi : Nat) : Bool :=
  strictB (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) yi r) y) fun z =>
    CFSG.KLie.CT.notB (allN 4 fun i => CFSG.KLie.CT.notB (notInK 64 TT (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) z (TG i)) z)))

@[expose] noncomputable def witK (G BT : Nat → Nat) (r y k : Nat) : Bool :=
  syl2Wit.any fun e => CFSG.KLie.CT.andB (Nat.beq e.1 k) (strictB (wK G e.2) fun c =>
    strictB (pinvS 42 6 (mask 6) c) fun ci =>
      CFSG.KLie.CT.andB (commPt 42 6 c r) (CFSG.KLie.CT.andB (canonK 42 6 (mask 6) (42 * 6) ci)
        (CFSG.KLie.CT.andB (Nat.beq (pcomp 42 6 (mask 6) c ci) (pidn 42 6))
          (CFSG.KLie.CT.notB (notInK 192 BT (pcomp 42 6 (mask 6) ci y))))))

@[expose] noncomputable def syl2K (G TT TG BT Y YI : Nat → Nat) (r : Nat) : Bool :=
  strictB r fun r => allN 105 fun k => strictB (Y k) fun y =>
    CFSG.KLie.CT.orB (nnK TT TG r y (YI k)) (witK G BT r y k)

@[expose] noncomputable def fieldK (G : Nat → Nat) (r : Nat) : Bool :=
  strictB (pidn 42 6) fun e => strictB r fun r =>
  strictB (tgK G 0) fun z0 => strictB (tgK G 4) fun z4 => strictB (tgK G 8) fun z8 =>
  strictB (tgK G 12) fun z12 =>
  allN 64 fun k => strictB (tgK G k) fun t =>
    CFSG.KLie.CT.orB (CFSG.KLie.CT.notB (Nat.beq (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) r t) r) t) e))
      (CFSG.KLie.CT.notB (allN 64 fun m => strictB (tgK G m) fun u => strictB (pinvS 42 6 (mask 6) u) fun ui =>
        CFSG.KLie.CT.notB (CFSG.KLie.CT.andB (CFSG.KLie.CT.andB (canonK 42 6 (mask 6) (42 * 6) ui) (Nat.beq (pcomp 42 6 (mask 6) u ui) e))
          (strictB (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) (pcomp 42 6 (mask 6) u r) ui) r)
            fun X => CFSG.KLie.CT.orB (Nat.beq t (pcomp 42 6 (mask 6) X z0))
              (CFSG.KLie.CT.orB (Nat.beq t (pcomp 42 6 (mask 6) X z4))
                (CFSG.KLie.CT.orB (Nat.beq t (pcomp 42 6 (mask 6) X z8))
                  (Nat.beq t (pcomp 42 6 (mask 6) X z12))))))))

end CFSG.KC.L34Field

end
