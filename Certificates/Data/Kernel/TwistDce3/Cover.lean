module

public import Certificates.Data.Kernel.TwistDce3.Defs
public import Certificates.Data.Kernel.TwistDce2.Rels

public section

namespace CFSG.KC.TwDce3

open CFSG.KC.TwDce hiding evP isOne pathW wsK wsFail wsJ wsMk wsBad dKind dN1 dN2 isFact walkRun
  walkOK recOK nodesOK foldStep foldRange
open CFSG.KC.TwDce2 hiding evP isOne tStep posStep walkRun walkOK recOK foldStep foldRange
  lettersOK coverK coverRange relsOK fixAll stabRange

section
variable (PB : Nat) (F : Nat → Nat) (INVM : Nat) (RD RW : Nat → Nat)

@[expose] noncomputable def lettersOK (NL NP : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun c acc => andB acc (andB (Nat.blt (ivL INVM c) NL)
      (Nat.rec (motive := fun _ => Bool) true
        (fun x acc2 => andB acc2 (TwDce.sB (CFSG.KC.YModel.fieldAt PB (F c) x) (fun y =>
          andB (Nat.blt y NP)
            (Nat.beq (CFSG.KC.YModel.fieldAt PB (F (ivL INVM c)) y) x)))) NP)))
    NL

@[expose] noncomputable def fixAll (NP w : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun x acc => andB acc (Nat.beq (evP PB F w x) x)) NP

@[expose] noncomputable def relsOK (NP : Nat) (ws : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun w _ acc => andB (andB (codesOK w) (TwDce.sB (codesW w) (fun v => fixAll PB F NP v))) acc)
    ws

@[expose] noncomputable def coverK (NP n : Nat) (DS : List Nat) (k : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun mask => Nat.beq mask (ones NP))
    (fun e _ ih mask =>
      Bool.rec (motive := fun _ => Bool)
        (TwDce.sB (fld e (nat_lit 1) (ones (nat_lit 21))) (fun c =>
          TwDce.sB (Nat.shiftRight e (nat_lit 22)) (fun p =>
            andB (andB (isStabOf RD n k (Nat.shiftRight c (nat_lit 1)))
                (Nat.beq (fld mask p (nat_lit 1)) (nat_lit 1)))
              (TwDce.sB (evP PB F (gWord INVM RW c) p) (fun x =>
                TwDce.sB (Nat.lor mask (Nat.shiftLeft (nat_lit 1) x)) ih)))))
        (TwDce.sB (Nat.shiftRight e (nat_lit 1)) (fun f => TwDce.sB (RD f) (fun d =>
          andB (andB (Nat.blt f n) (andB (isFact (dKind d))
              (andB (Nat.beq (dN1 d) k) (CFSG.KC.LaneChain.memN (dN2 d) DS))))
            (TwDce.sB (evP PB F (wInv INVM (RW f)) (nat_lit 0)) (fun x =>
              TwDce.sB (Nat.lor mask (Nat.shiftLeft (nat_lit 1) x)) ih)))))
        (Nat.beq (Nat.land e (nat_lit 1)) (nat_lit 1)))
    L (nat_lit 0)

@[expose] noncomputable def coverRange (NP n : Nat) (DS : List Nat) (CV : List (List Nat))
    (a m : Nat) : Bool :=
  allRange (fun i => coverK PB F INVM RD RW NP n DS (CFSG.KC.LaneChain.getN DS i)
    (CFSG.KC.LaneChain.getL CV i)) a m

end

@[expose] noncomputable def stabRange (FB : Nat → Nat) (INVM NQ : Nat) (RD RW : Nat → Nat)
    (n : Nat) (DS : List Nat) (CG : List (List Nat)) (CW CB CS CT : List (List (List Nat)))
    (CN : List Nat) (a m : Nat) : Bool :=
  allRange (fun i => stabOK FB INVM NQ RD RW n (CFSG.KC.LaneChain.getN DS i)
    (CFSG.KC.LaneChain.getL CG i) (getLL CW i) (getLL CB i) (getLL CS i) (getLL CT i)
    (CFSG.KC.LaneChain.getN CN i)) a m

@[expose] noncomputable def repackOK (PB : Nat) (F FB : Nat → Nat) (NL NQ : Nat) : Bool :=
  allRange (fun c => allRange (fun x => Nat.beq (CFSG.KC.YModel.fieldAt (nat_lit 11) (FB c) x)
    (CFSG.KC.YModel.fieldAt PB (F c) x)) (nat_lit 0) NQ) (nat_lit 0) NL

end CFSG.KC.TwDce3

end
