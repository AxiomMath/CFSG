module

public import Certificates.Data.Kernel.L34W.Tab42
public import Certificates.Data.Kernel.L34W.Model
public import Certificates.Data.Kernel.L34W.Outer
public import Certificates.Data.Kernel.Spor.Prim
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsParabolicCertInputs

public section

namespace CFSG.KC.L34Cov

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.L34W
open CFSG.ComponentClassification.GrSLit.L34Facts

@[expose] noncomputable def sgAbW (AB : Nat → Nat) (w : List Nat) : Nat :=
  pword AB w (pidn (nat_lit 42) (nat_lit 6))

@[expose] noncomputable def sgInvOK (g gi : Nat) : Bool :=
  bAnd(canonK (nat_lit 42) (nat_lit 6) (mask 6) (nat_lit 252) gi,
    Nat.beq (pcomp (nat_lit 42) (nat_lit 6) (mask 6) g gi) (pidn (nat_lit 42) (nat_lit 6)))

@[expose] noncomputable def sgConjW (AB : Nat → Nat) (w : List Nat) (r g : Nat) : Bool :=
  Nat.beq (pcomp (nat_lit 42) (nat_lit 6) (mask 6) (sgAbW AB w) r)
    (pcomp (nat_lit 42) (nat_lit 6) (mask 6) r g)

@[expose] noncomputable def sgAbOK (G AB : Nat → Nat) (UA UB : List (List Nat)) : Bool :=
  bAnd(bAnd(Nat.beq (AB (nat_lit 0)) (pword (gS G) wa (pidn (nat_lit 42) (nat_lit 6))),
      Nat.beq (AB (nat_lit 2)) (pword (gS G) wb (pidn (nat_lit 42) (nat_lit 6)))),
    bAnd(bAnd(sgInvOK (AB (nat_lit 0)) (AB (nat_lit 1)), sgInvOK (AB (nat_lit 2)) (AB (nat_lit 3))),
      allN (nat_lit 36) fun i => strictB (repK G i) fun r =>
        bAnd(sgConjW AB (UA.getD i []) r (AB (nat_lit 0)),
          sgConjW AB (UB.getD i []) r (AB (nat_lit 2)))))

@[expose] noncomputable def sgCjOK (G Y A : Nat → Nat) : Bool :=
  allN (nat_lit 36) fun i => strictB (repK G i) fun r => allN (nat_lit 64) fun t =>
    Nat.beq (pcomp (nat_lit 42) (nat_lit 6) (mask 6) r (Y t))
      (Y (Nat.add (Nat.mul (nat_lit 64) i) (Nat.div (ent A i t) (nat_lit 48))))

@[expose] noncomputable def sgT0K (G : Nat → Nat) (g : Nat) : Nat :=
  pword (gS G) (wT₀.getD g []) (pidn (nat_lit 42) (nat_lit 6))

@[expose] noncomputable def sgFixOK (G : Nat → Nat) : Bool :=
  bAnd(allN (nat_lit 4) fun g => strictB (sgT0K G g) fun x =>
      bAnd(Nat.beq (pg (nat_lit 6) (mask 6) x (nat_lit 2)) (nat_lit 2),
        Nat.beq (pg (nat_lit 6) (mask 6) x (nat_lit 23)) (nat_lit 23)),
    allN (nat_lit 42) fun p => bIf(Nat.beq p (nat_lit 2), true, bIf(Nat.beq p (nat_lit 23), true,
      bNot (allN (nat_lit 4) fun g => Nat.beq (pg (nat_lit 6) (mask 6) (sgT0K G g) p) p))))

@[expose] noncomputable def sgOF (O : Nat → Nat) (k f : Nat) : Nat := pg (nat_lit 7) (mask 7) (O k) f

@[expose] noncomputable def sgOKey (O : Nat → Nat) (k : Nat) : Nat :=
  Nat.add (Nat.mul (nat_lit 64) (sgOF O k (nat_lit 2))) (sgOF O k (nat_lit 3))

@[expose] noncomputable def sgOStep (G O : Nat → Nat) (k : Nat) : Bool :=
  strictB (sgOF O k (nat_lit 0)) fun p => strictB (sgOF O k (nat_lit 1)) fun j =>
  strictB (sgOF O k (nat_lit 2)) fun a => strictB (sgOF O k (nat_lit 3)) fun b =>
  strictB (pg (nat_lit 6) (mask 6) (G j) (sgOF O p (nat_lit 2))) fun x =>
  strictB (pg (nat_lit 6) (mask 6) (G j) (sgOF O p (nat_lit 3))) fun y =>
    bAnd(bAnd(Nat.blt p k, Nat.blt j (nat_lit 6)), bAnd(bAnd(Nat.blt a b, Nat.blt b (nat_lit 42)),
      bIf(bAnd(Nat.beq x a, Nat.beq y b), true, bAnd(Nat.beq x b, Nat.beq y a))))

@[expose] noncomputable def sgOrbOK (G O : Nat → Nat) : Bool :=
  bAnd(bAnd(Nat.beq (sgOF O (nat_lit 0) (nat_lit 2)) (nat_lit 2),
      Nat.beq (sgOF O (nat_lit 0) (nat_lit 3)) (nat_lit 23)),
    bAnd(allN (nat_lit 104) fun k => sgOStep G O (Nat.succ k),
      allN (nat_lit 105) fun k => strictB (sgOKey O k) fun c =>
        allN k fun k' => bNot (Nat.beq (sgOKey O k') c)))

@[expose] noncomputable def sgStabOK (Y : Nat → Nat) : Bool :=
  allN (nat_lit 2304) fun n => strictB (pg (nat_lit 6) (mask 6) (Y n) (nat_lit 2)) fun x =>
    strictB (pg (nat_lit 6) (mask 6) (Y n) (nat_lit 23)) fun y =>
      bIf(bAnd(Nat.beq x (nat_lit 2), Nat.beq y (nat_lit 23)), true,
        bAnd(Nat.beq x (nat_lit 23), Nat.beq y (nat_lit 2)))

@[expose] noncomputable def sgSortOK (Y P Q : Nat → Nat) : Bool :=
  bAnd(allN (nat_lit 2303) fun k => Nat.blt (Y (P k)) (Y (P (Nat.succ k))),
    allN (nat_lit 2304) fun n => strictB (Q n) fun q => bAnd(Nat.blt q (nat_lit 2304), Nat.beq (P q) n))

end CFSG.KC.L34Cov

end
