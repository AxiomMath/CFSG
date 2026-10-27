module

public import Certificates.Data.Kernel.TwistDce2.Defs
public import Certificates.Data.Kernel.LaneChain

public section

namespace CFSG.KC.TwDce2

open CFSG.KC.TwDce

@[expose] noncomputable def getLL (l : List (List (List Nat))) : Nat → List (List Nat) :=
  List.rec (motive := fun _ => Nat → List (List Nat)) (fun _ => List.nil)
    (fun x _ ih i => Nat.rec (motive := fun _ => List (List Nat)) x (fun j _ => ih j) i) l

@[expose] noncomputable def allRange (P : Nat → Bool) (a m : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun j acc => andB acc (P (Nat.add a j))) m

section
variable (F : Nat → Nat) (INVM NP : Nat) (RD RW : Nat → Nat)

@[expose] noncomputable def ptL (c x : Nat) : Nat := CFSG.KC.YModel.fieldAt (nat_lit 11) (F c) x

@[expose] noncomputable def lettersOK : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun c acc => andB acc (andB (Nat.blt (ivL INVM c) (nat_lit 12))
      (Nat.rec (motive := fun _ => Bool) true
        (fun x acc2 => andB acc2 (TwDce.sB (ptL F c x) (fun y =>
          andB (Nat.blt y NP) (Nat.beq (ptL F (ivL INVM c) y) x)))) NP)))
    (nat_lit 12)

@[expose] noncomputable def isStabOf (n k g : Nat) : Bool :=
  andB (Nat.blt g n) (TwDce.sB (RD g) (fun d =>
    andB (isEq (dKind d)) (andB (Nat.beq (dN1 d) k) (Nat.beq (dN2 d) k))))

@[expose] noncomputable def gWord (c : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (RW (Nat.shiftRight c (nat_lit 1)))
    (wInv INVM (RW (Nat.shiftRight c (nat_lit 1)))) (Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 1))

@[expose] noncomputable def coverK (n ND k : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun mask => Nat.beq mask (ones NP))
    (fun e _ ih mask =>
      Bool.rec (motive := fun _ => Bool)
        (TwDce.sB (fld e (nat_lit 1) (ones (nat_lit 21))) (fun c =>
          TwDce.sB (Nat.shiftRight e (nat_lit 22)) (fun p =>
            andB (andB (isStabOf RD n k (Nat.shiftRight c (nat_lit 1)))
                (Nat.beq (fld mask p (nat_lit 1)) (nat_lit 1)))
              (TwDce.sB (evP F (gWord INVM RW c) p) (fun x =>
                TwDce.sB (Nat.lor mask (Nat.shiftLeft (nat_lit 1) x)) ih)))))
        (TwDce.sB (Nat.shiftRight e (nat_lit 1)) (fun f => TwDce.sB (RD f) (fun d =>
          andB (andB (Nat.blt f n) (andB (isFact (dKind d))
              (andB (Nat.beq (dN1 d) k) (Nat.blt (dN2 d) ND))))
            (TwDce.sB (evP F (wInv INVM (RW f)) (nat_lit 0)) (fun x =>
              TwDce.sB (Nat.lor mask (Nat.shiftLeft (nat_lit 1) x)) ih)))))
        (Nat.beq (Nat.land e (nat_lit 1)) (nat_lit 1)))
    L (nat_lit 0)

@[expose] noncomputable def coverRange (n ND : Nat) (CV : List (List Nat)) (a m : Nat) : Bool :=
  allRange (fun k => coverK F INVM NP RD RW n ND k (CFSG.KC.LaneChain.getL CV k)) a m

@[expose] noncomputable def wmul (g h : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Nat.mul (nat_lit 2) (evP F (Nat.shiftRight g (nat_lit 1)) (Nat.shiftRight h (nat_lit 1))))
    (Nat.add (Nat.mul (nat_lit 2)
      (wCat (Nat.shiftRight h (nat_lit 1)) (Nat.shiftRight g (nat_lit 1)))) (nat_lit 1))
    (Nat.beq (Nat.land h (nat_lit 1)) (nat_lit 1))

@[expose] noncomputable def wvld (x : Nat) : Bool :=
  andB (Nat.beq (Nat.land x (nat_lit 1)) (nat_lit 0)) (Nat.blt (Nat.shiftRight x (nat_lit 1)) NP)

@[expose] noncomputable def gRegs (L : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun c _ ih => List.cons (Nat.add (Nat.mul (nat_lit 2) (gWord INVM RW c)) (nat_lit 1)) ih) L

@[expose] noncomputable def treeB (M : List Nat) (nreg : Nat) (G : List Nat) (k : Nat → Bool)
    (T : List Nat) : Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Bool)
    (fun pend _ cnt => andB (Nat.beq pend (nat_lit 0)) (k cnt))
    (fun c _ ih pend mask cnt => Nat.rec (motive := fun _ => Bool)
      (andB (Nat.beq (fld mask c (nat_lit 1)) (nat_lit 1)) (ih (Nat.succ c) mask cnt))
      (fun p _ => andB (andB (CFSG.KC.LaneChain.memN c G) (Nat.blt c nreg))
        (TwDce.sB (Nat.shiftRight (wmul F (CFSG.KC.LaneChain.getR M nreg c)
            (Nat.mul (nat_lit 2) p)) (nat_lit 1)) (fun v =>
          andB (Nat.beq (fld mask v (nat_lit 1)) (nat_lit 0))
            (TwDce.sB (Nat.lor mask (Nat.shiftLeft (nat_lit 1) v)) (fun m =>
              ih (nat_lit 0) m (Nat.succ cnt))))))
      pend) T

@[expose] noncomputable def levelsB (M : List Nat) (nreg : Nat) (Xs : List Nat) (tot : Nat)
    (Ts : List (List Nat)) (Gs : List (List Nat)) : Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) (fun _ acc => Nat.beq acc tot)
    (fun G _ ih k acc => andB (andB (Nat.blt k (CFSG.KC.Ord.lenL Xs))
        (CFSG.KC.LaneChain.gensK (wmul F) M Xs G nreg k))
      (treeB F M nreg G (fun n => ih (Nat.succ k) (Nat.mul acc n))
        (CFSG.KC.LaneChain.getL Ts k) (nat_lit 0)
        (Nat.shiftLeft (nat_lit 1) (Nat.shiftRight (CFSG.KC.LaneChain.getN Xs k) (nat_lit 1)))
        (nat_lit 1))) Gs

@[expose] noncomputable def chainB (W Bs Gs Ts : List (List Nat)) (M₀ : List Nat) (tot : Nat) :
    Bool :=
  CFSG.KC.LaneChain.regsK (wmul F) (fun M nreg => CFSG.KC.LaneChain.basesK (wvld NP) (nat_lit 11)
      (fun Xs => levelsB F M nreg Xs tot Ts Gs (nat_lit 0) (nat_lit 1)) Bs List.nil)
    W M₀ (CFSG.KC.Ord.lenL M₀)

@[expose] noncomputable def stabOK (n k : Nat) (CG : List Nat) (W Bs Gs Ts : List (List Nat))
    (tot : Nat) : Bool :=
  andB (List.rec (motive := fun _ => Bool) true
      (fun c _ ih => andB (isStabOf RD n k (Nat.shiftRight c (nat_lit 1))) ih) CG)
    (chainB F NP W Bs Gs Ts (gRegs INVM RW CG) tot)

@[expose] noncomputable def stabRange (n : Nat) (CG : List (List Nat))
    (CW CB CS CT : List (List (List Nat))) (CN : List Nat) (a m : Nat) : Bool :=
  allRange (fun k => stabOK F INVM NP RD RW n k (CFSG.KC.LaneChain.getL CG k) (getLL CW k)
    (getLL CB k) (getLL CS k) (getLL CT k) (CFSG.KC.LaneChain.getN CN k)) a m

end

end CFSG.KC.TwDce2

end
