module

public import Certificates.Data.Kernel.TwistDce3.Cover

public section

namespace CFSG.KC.TwDce3

open CFSG.KC.TwDce hiding evP isOne pathW wsK wsFail wsJ wsMk wsBad dKind dN1 dN2 isFact walkRun
  walkOK recOK nodesOK foldStep foldRange
open CFSG.KC.TwDce2 hiding evP isOne tStep posStep walkRun walkOK recOK foldStep foldRange
  lettersOK coverK coverRange relsOK fixAll stabRange

@[expose] noncomputable def saltStep (e : Nat) : Nat :=
  Nat.land (Nat.mul (Nat.add e (nat_lit 1)) (nat_lit 11400714819323198485)) (ones (nat_lit 64))

section
variable (PB : Nat) (F : Nat → Nat) (INVM : Nat) (RD RW : Nat → Nat)

@[expose] noncomputable def coverKS (NP n : Nat) (DS : List Nat) (k : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool)
    (fun s => Nat.beq (Nat.shiftRight s (nat_lit 64)) (ones NP))
    (fun e _ ih s =>
      Bool.rec (motive := fun _ => Bool)
        (TwDce.sB (fld e (nat_lit 1) (ones (nat_lit 21))) (fun c =>
          TwDce.sB (Nat.shiftRight e (nat_lit 22)) (fun p =>
            andB (andB (isStabOf RD n k (Nat.shiftRight c (nat_lit 1)))
                (Nat.beq (fld s (Nat.add p (nat_lit 64)) (nat_lit 1)) (nat_lit 1)))
              (TwDce.sB (evP PB F (gWord INVM RW c) p) (fun x =>
                TwDce.sB (Nat.xor (Nat.lor s (Nat.shiftLeft (nat_lit 1) (Nat.add x (nat_lit 64))))
                  (saltStep e)) ih)))))
        (TwDce.sB (Nat.shiftRight e (nat_lit 1)) (fun f => TwDce.sB (RD f) (fun d =>
          andB (andB (Nat.blt f n) (andB (isFact (dKind d))
              (andB (Nat.beq (dN1 d) k) (CFSG.KC.LaneChain.memN (dN2 d) DS))))
            (TwDce.sB (evP PB F (wInv INVM (RW f)) (nat_lit 0)) (fun x =>
              TwDce.sB (Nat.xor (Nat.lor s (Nat.shiftLeft (nat_lit 1) (Nat.add x (nat_lit 64))))
                (saltStep e)) ih)))))
        (Nat.beq (Nat.land e (nat_lit 1)) (nat_lit 1)))
    L (nat_lit 9876543210123456789)

@[expose] noncomputable def coverRangeS (NP n : Nat) (DS : List Nat) (CV : List (List Nat))
    (a m : Nat) : Bool :=
  allRange (fun i => coverKS PB F INVM RD RW NP n DS (CFSG.KC.LaneChain.getN DS i)
    (CFSG.KC.LaneChain.getL CV i)) a m

end

end CFSG.KC.TwDce3

end
