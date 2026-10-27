module

public import Certificates.Data.Kernel.SmithD6.MeetK
public import Certificates.Data.SmithD6RhoData

public section

namespace CFSG.KD.SmithD6

open CFSG.SmithD6 CFSG.KC.KeyTree

@[expose] noncomputable def kcDist (c : Nat) : Nat :=
  nIf(Nat.beq c 1, 3, nIf(Nat.beq c 4, 2, nIf(Nat.beq c 16, 1, 0)))

@[expose] noncomputable def d6RankRow (R i : Nat) : List Nat → List Nat → Nat :=
  List.rec (motive := fun _ => List Nat → Nat) (fun _ => 0)
    (fun j _ ih invs => List.rec (motive := fun _ => Nat) 0
      (fun v invs' _ => Nat.xor (nIf(Nat.beq (fld(R, kcDist (d6MeetK i j), 1)) 1, v, 0))
        (ih invs')) invs)

@[expose] noncomputable def d6RankGo (R : Nat) (cc inv : List Nat) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun i _ ih s => bAnd(Nat.beq (d6RankRow R i cc inv) (Nat.pow 2 s), ih (Nat.succ s)))

@[expose] noncomputable def d6RankOK (r : Nat) : Bool :=
  d6RankGo (rankRels.toList.getD r 0) (rankCols.toList.getD r #[]).toList
    (rankInv.toList.getD r #[]).toList (rankRows.toList.getD r #[]).toList 0

end CFSG.KD.SmithD6

end
