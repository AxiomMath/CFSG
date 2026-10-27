module

public import Certificates.Data.Kernel.TwistDce3.Cover
public import CFSG.Certificates.Kernel.MonsterConv.PermValid

public section

namespace CFSG.KC.TwDce3

open CFSG.KC.TwDce hiding evP isOne pathW wsK wsFail wsJ wsMk wsBad dKind dN1 dN2 isFact walkRun
  walkOK recOK nodesOK foldStep foldRange
open CFSG.KC.TwDce2 hiding evP isOne tStep posStep walkRun walkOK recOK foldStep foldRange
  lettersOK coverK coverRange relsOK fixAll stabRange

@[expose] noncomputable def tabPlaneN (K NP RAW b : Nat) : Nat :=
  Nat.lor
    (Nat.land (MonsterConv.Perm.rawPlane RAW K (Nat.shiftLeft (nat_lit 1) K) K (nat_lit 0) b)
      (MonsterConv.Perm.ones NP))
    (Nat.land (MonsterConv.Perm.idPlane (Nat.shiftLeft (nat_lit 1) K) b)
      (Nat.xor (MonsterConv.Perm.ones (Nat.shiftLeft (nat_lit 1) K)) (MonsterConv.Perm.ones NP)))

@[expose] noncomputable def tabPlanesN (K NP RAW : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun b acc => Nat.lor acc (Nat.shiftLeft (tabPlaneN K NP RAW b)
      (Nat.mul b (Nat.shiftLeft (nat_lit 1) K)))) K

@[expose] noncomputable def bindN (K NP RAW N : Nat) : Bool :=
  andB (MonsterConv.Perm.netValid K N)
    (Nat.beq (MonsterConv.Perm.netApply K (Nat.shiftLeft (nat_lit 1) K)
        (MonsterConv.Perm.repU (Nat.shiftLeft (nat_lit 1) K) K) N (MonsterConv.Perm.idP K))
      (tabPlanesN K NP RAW))

@[expose] noncomputable def bindAll (K NP NL : Nat) (F NS : Nat → Nat) : Bool :=
  allRange (fun c => bindN K NP (F c) (NS c)) (nat_lit 0) NL

@[expose] noncomputable def saltN (K : Nat) : Nat :=
  Nat.mod (Nat.pow (nat_lit 3) (Nat.shiftLeft (nat_lit 1) K))
    (Nat.shiftLeft (nat_lit 1) (Nat.shiftLeft (nat_lit 1) K))

section
variable (PB : Nat) (F : Nat → Nat) (INVM : Nat) (RD RW NS : Nat → Nat) (K : Nat)

@[expose] noncomputable def wSetN (w X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun _ ih s x => TwDce.sN (MonsterConv.Perm.netApply K (Nat.shiftLeft (nat_lit 1) K)
        (MonsterConv.Perm.repU (Nat.shiftLeft (nat_lit 1) K) (nat_lit 2))
        (NS (ivL INVM (Nat.land s (nat_lit 15)))) x)
      (fun y => TwDce.sN (Nat.shiftRight s (nat_lit 4)) (fun s' => ih s' y)))
    (wLen w) (wStr w) X

@[expose] noncomputable def appsN (NL NP n k : Nat) (AL : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool)
    (fun X => Nat.beq (Nat.land (Nat.shiftRight X (Nat.shiftLeft (nat_lit 1) K)) (ones NP))
      (ones NP))
    (fun c _ ih X => TwDce.sB (gWord INVM RW c) (fun w =>
      andB (andB (isStabOf RD n k (Nat.shiftRight c (nat_lit 1))) (wBelow NL w))
        (TwDce.sB (wSetN INVM NS K w X) (fun Y =>
          TwDce.sB (Nat.lor Y (Nat.land X (Nat.shiftLeft (ones (Nat.shiftLeft (nat_lit 1) K))
            (Nat.shiftLeft (nat_lit 1) K)))) ih))))
    AL

@[expose] noncomputable def rootsN (NL NP n : Nat) (DS : List Nat) (k : Nat) (RL AL : List Nat) :
    Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool)
    (fun X => appsN INVM RD RW NS K NL NP n k AL X)
    (fun f _ ih X => TwDce.sB (RD f) (fun d =>
      andB (andB (Nat.blt f n) (andB (isFact (dKind d))
          (andB (Nat.beq (dN1 d) k) (CFSG.KC.LaneChain.memN (dN2 d) DS))))
        (TwDce.sB (evP PB F (wInv INVM (RW f)) (nat_lit 0)) (fun x =>
          TwDce.sB (Nat.lor X (Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.shiftLeft (nat_lit 1) K) x)))
            ih))))
    RL

@[expose] noncomputable def coverNK (NL NP n : Nat) (DS : List Nat) (k : Nat) (RL AL : List Nat) :
    Bool :=
  rootsN PB F INVM RD RW NS K NL NP n DS k RL AL (saltN K)

@[expose] noncomputable def coverRangeN (NL NP n : Nat) (DS : List Nat) (CR CA : List (List Nat))
    (a m : Nat) : Bool :=
  allRange (fun i => coverNK PB F INVM RD RW NS K NL NP n DS (CFSG.KC.LaneChain.getN DS i)
    (CFSG.KC.LaneChain.getL CR i) (CFSG.KC.LaneChain.getL CA i)) a m

end

end CFSG.KC.TwDce3

end
