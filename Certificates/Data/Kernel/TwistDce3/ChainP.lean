module

public import Certificates.Data.Kernel.TwistDce3.Defs
public import Certificates.Data.Kernel.TwistDce2.Cover

public section

namespace CFSG.KC.TwDce3

open CFSG.KC.TwDce hiding evP isOne pathW wsK wsFail wsJ wsMk wsBad dKind dN1 dN2 isFact walkRun
  walkOK recOK nodesOK foldStep foldRange
open CFSG.KC.TwDce2 hiding evP isOne tStep posStep walkRun walkOK recOK foldStep foldRange

section
variable (PB : Nat) (F : Nat → Nat) (INVM NP : Nat) (RD RW : Nat → Nat)

@[expose] noncomputable def wmulP (g h : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Nat.mul (nat_lit 2) (evP PB F (Nat.shiftRight g (nat_lit 1)) (Nat.shiftRight h (nat_lit 1))))
    (Nat.add (Nat.mul (nat_lit 2)
      (wCat (Nat.shiftRight h (nat_lit 1)) (Nat.shiftRight g (nat_lit 1)))) (nat_lit 1))
    (Nat.beq (Nat.land h (nat_lit 1)) (nat_lit 1))

@[expose] noncomputable def treeBP (M : List Nat) (nreg : Nat) (G : List Nat) (k : Nat → Bool)
    (T : List Nat) : Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Bool)
    (fun pend _ cnt => andB (Nat.beq pend (nat_lit 0)) (k cnt))
    (fun c _ ih pend mask cnt => Nat.rec (motive := fun _ => Bool)
      (andB (Nat.beq (fld mask c (nat_lit 1)) (nat_lit 1)) (ih (Nat.succ c) mask cnt))
      (fun p _ => andB (andB (CFSG.KC.LaneChain.memN c G) (Nat.blt c nreg))
        (TwDce.sB (Nat.shiftRight (wmulP PB F (CFSG.KC.LaneChain.getR M nreg c)
            (Nat.mul (nat_lit 2) p)) (nat_lit 1)) (fun v =>
          andB (Nat.beq (fld mask v (nat_lit 1)) (nat_lit 0))
            (TwDce.sB (Nat.lor mask (Nat.shiftLeft (nat_lit 1) v)) (fun m =>
              ih (nat_lit 0) m (Nat.succ cnt))))))
      pend) T

@[expose] noncomputable def levelsBP (M : List Nat) (nreg : Nat) (Xs : List Nat) (tot : Nat)
    (Ts : List (List Nat)) (Gs : List (List Nat)) : Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) (fun _ acc => Nat.beq acc tot)
    (fun G _ ih k acc => andB (andB (Nat.blt k (CFSG.KC.Ord.lenL Xs))
        (CFSG.KC.LaneChain.gensK (wmulP PB F) M Xs G nreg k))
      (treeBP PB F M nreg G (fun n => ih (Nat.succ k) (Nat.mul acc n))
        (CFSG.KC.LaneChain.getL Ts k) (nat_lit 0)
        (Nat.shiftLeft (nat_lit 1) (Nat.shiftRight (CFSG.KC.LaneChain.getN Xs k) (nat_lit 1)))
        (nat_lit 1))) Gs

@[expose] noncomputable def chainBP (W Bs Gs Ts : List (List Nat)) (M₀ : List Nat) (tot : Nat) :
    Bool :=
  CFSG.KC.LaneChain.regsK (wmulP PB F) (fun M nreg => CFSG.KC.LaneChain.basesK (wvld NP) PB
      (fun Xs => levelsBP PB F M nreg Xs tot Ts Gs (nat_lit 0) (nat_lit 1)) Bs List.nil)
    W M₀ (CFSG.KC.Ord.lenL M₀)

@[expose] noncomputable def stabOKP (n k : Nat) (CG : List Nat) (W Bs Gs Ts : List (List Nat))
    (tot : Nat) : Bool :=
  andB (List.rec (motive := fun _ => Bool) true
      (fun c _ ih => andB (isStabOf RD n k (Nat.shiftRight c (nat_lit 1))) ih) CG)
    (chainBP PB F NP W Bs Gs Ts (gRegs INVM RW CG) tot)

@[expose] noncomputable def stabRangeP (n : Nat) (DS : List Nat) (CG : List (List Nat))
    (CW CB CS CT : List (List (List Nat))) (CN : List Nat) (a m : Nat) : Bool :=
  allRange (fun i => stabOKP PB F INVM NP RD RW n (CFSG.KC.LaneChain.getN DS i)
    (CFSG.KC.LaneChain.getL CG i) (getLL CW i) (getLL CB i) (getLL CS i) (getLL CT i)
    (CFSG.KC.LaneChain.getN CN i)) a m

end

end CFSG.KC.TwDce3

end
