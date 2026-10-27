module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.PackPerm

@[expose] noncomputable def pget (P i : Nat) : Nat := fld(P, Nat.mul 8 i, 255)

@[expose] noncomputable def pack8 (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ ih => Nat.lor x (Nat.shiftLeft ih 8)) l

@[expose] noncomputable def allLt (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => bAnd(f i, ih)) n

@[expose] noncomputable def entriesLt (d : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => bAnd(Nat.blt x d, ih)) l

@[expose] noncomputable def lanesInj (d P : Nat) : Bool :=
  allLt d fun x => allLt x fun y => bIf(Nat.beq (pget P x) (pget P y), false, true)

@[expose] noncomputable def wimg (P₀ P₁ : Nat) (w : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun i _ ih => pget (nIf(Nat.beq i 0, P₀, P₁)) ih) w

@[expose] noncomputable def eqOn (d P₀ P₁ : Nat) (u w : List Nat) : Bool :=
  allLt d fun x => Nat.beq (wimg P₀ P₁ u x) (wimg P₀ P₁ w x)

@[expose] noncomputable def moves (d P₀ P₁ : Nat) (u : List Nat) : Bool :=
  bIf(allLt d fun x => Nat.beq (wimg P₀ P₁ u x) x, false, true)

@[expose] noncomputable def tabOk (d : Nat) (l : List Nat) (P : Nat) : Bool :=
  bAnd(Nat.beq l.length d, bAnd(entriesLt d l, lanesInj d P))

@[expose] noncomputable def relCheckP (d : Nat) (l₀ l₁ : List Nat) (P₀ P₁ : Nat)
    (eqs : List (List Nat × List Nat)) (neqs : List (List Nat)) : Bool :=
  bAnd(Nat.ble d 256, bAnd(tabOk d l₀ P₀, bAnd(tabOk d l₁ P₁,
    bAnd(List.rec (motive := fun _ => Bool) true
        (fun e _ ih => bAnd(eqOn d P₀ P₁ e.1 e.2, ih)) eqs,
      List.rec (motive := fun _ => Bool) true (fun u _ ih => bAnd(moves d P₀ P₁ u, ih)) neqs))))

@[expose] noncomputable def relCheck (d : Nat) (l₀ l₁ : List Nat)
    (eqs : List (List Nat × List Nat)) (neqs : List (List Nat)) : Bool :=
  relCheckP d l₀ l₁ (pack8 l₀) (pack8 l₁) eqs neqs

end CFSG.KC.PackPerm

end
