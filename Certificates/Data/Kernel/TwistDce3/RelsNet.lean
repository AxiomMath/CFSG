module

public import Certificates.Data.Kernel.TwistDce3.CoverNet

public section

namespace CFSG.KC.TwDce3

open CFSG.KC.TwDce hiding evP isOne pathW wsK wsFail wsJ wsMk wsBad dKind dN1 dN2 isFact walkRun
  walkOK recOK nodesOK foldStep foldRange
open CFSG.KC.TwDce2 hiding evP isOne tStep posStep walkRun walkOK recOK foldStep foldRange
  lettersOK coverK coverRange relsOK fixAll stabRange

section
variable (INVM : Nat) (NS : Nat → Nat) (K : Nat)

@[expose] noncomputable def wPlN (P : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ x => x)
    (fun _ ih s x => TwDce.sN (MonsterConv.Perm.netApply K (Nat.shiftLeft (nat_lit 1) K)
        (MonsterConv.Perm.repU (Nat.shiftLeft (nat_lit 1) K) P)
        (NS (ivL INVM (Nat.land s (nat_lit 15)))) x)
      (fun y => TwDce.sN (Nat.shiftRight s (nat_lit 4)) (fun s' => ih s' y)))

@[expose] noncomputable def wIdN (v : Nat) : Bool :=
  Nat.beq (wPlN INVM NS K K (wLen v) (wStr v) (MonsterConv.Perm.idP K)) (MonsterConv.Perm.idP K)

@[expose] noncomputable def relsN (ws : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun w _ acc => andB (andB (codesOK w) (TwDce.sB (codesW w) (fun v => wIdN INVM NS K v))) acc)
    ws

end

end CFSG.KC.TwDce3

end
