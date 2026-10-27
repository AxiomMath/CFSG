module

public import Certificates.Data.Kernel.Misc.ArrEnum

public section

namespace CFSG.KC.PCent

open CFSG.KC.Enum (pg pcomp pidn allN)
open CFSG.KS (mask pinvS)

inductive PTree (α : Type) where
  | leaf : PTree α
  | node : PTree α → α → PTree α → PTree α

@[expose] def evensL {α : Type} : List α → List α
  | [] => []
  | [x] => [x]
  | x :: _ :: l => x :: evensL l

@[expose] def oddsL {α : Type} : List α → List α
  | [] => []
  | [_] => []
  | _ :: y :: l => y :: oddsL l

@[expose] def ofListT {α : Type} : Nat → List α → PTree α
  | 0, _ => .leaf
  | _ + 1, [] => .leaf
  | n + 1, x :: l => .node (ofListT n (evensL l)) x (ofListT n (oddsL l))

@[expose] def treeOf {α : Type} (L : List α) : PTree α := ofListT L.length L

@[expose] def getT {α : Type} [Inhabited α] : PTree α → Nat → α
  | .leaf, _ => default
  | .node _ x _, 0 => x
  | .node l _ r, i + 1 => if i % 2 = 0 then getT l (i / 2) else getT r (i / 2)

abbrev Rec := Nat × Nat × Nat × Nat

@[expose] def recK (ACT : Nat → Nat → Nat) (ngen N root : Nat) (r q : Rec) : Bool :=
  (Nat.beq r.2.1 (nat_lit 0) && Nat.beq r.1 root) ||
    (Nat.blt r.2.2.2 N && Nat.blt r.2.2.1 ngen && Nat.blt q.2.1 r.2.1 &&
      Nat.beq r.1 (ACT r.2.2.1 q.1))

@[expose] noncomputable def walkK (ACT : Nat → Nat → Nat) (ngen N root : Nat) (T : PTree Rec) :
    List Rec → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun r _ ih lo => Nat.ble lo r.1 && recK ACT ngen N root r (getT T r.2.2.2) &&
      ih (Nat.add r.1 (nat_lit 1)))

@[expose] noncomputable def orbRecK (ACT : Nat → Nat → Nat) (ngen root : Nat) (R : List Rec) : Bool :=
  walkK ACT ngen R.length root (treeOf R) R (nat_lit 0)

@[expose] noncomputable def conjI (n w : Nat) (G GI : Nat → Nat) (k y : Nat) : Nat :=
  pcomp n w (mask w) (G k) (pcomp n w (mask w) y (GI k))

@[expose] noncomputable def classK (n w : Nat) (G GI : Nat → Nat) (ngen v : Nat)
    (R : List Rec) : Bool :=
  allN ngen (fun k => Nat.beq (GI k) (pinvS n w (mask w) (G k))) &&
    orbRecK (conjI n w G GI) ngen v R

@[expose] noncomputable def pointOrbK (n w : Nat) (H : Nat → Nat) (ngen x : Nat) (R : List Rec) :
    Bool :=
  Nat.blt x n && orbRecK (fun k y => pg w (mask w) (H k) y) ngen x R

@[expose] noncomputable def wordK (n w : Nat) (G : Nat → Nat) (ws : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (pidn n w) (fun k _ ih => pcomp n w (mask w) (G k) ih) ws

@[expose] noncomputable def allL (f : Nat → Bool) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => f x && ih) l

@[expose] noncomputable def levelK (n w : Nat) (G : Nat → Nat) (ngen : Nat) (pre : List Nat)
    (lv : Nat × List Nat × List (List Nat) × List Rec) : Bool :=
  Nat.beq lv.2.1.length lv.2.2.1.length &&
    allN lv.2.1.length (fun k => Nat.beq (lv.2.1.getD k 0) (wordK n w G (lv.2.2.1.getD k [])) &&
      allL (fun c => Nat.blt c ngen) (lv.2.2.1.getD k []) &&
      allL (fun b => Nat.beq (pg w (mask w) (lv.2.1.getD k 0) b) b) pre) &&
    pointOrbK n w (fun k => lv.2.1.getD k 0) lv.2.1.length lv.1 lv.2.2.2

@[expose] noncomputable def levelsK (n w : Nat) (G : Nat → Nat) (ngen : Nat) :
    List (Nat × List Nat × List (List Nat) × List Rec) → List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun lv _ ih pre => levelK n w G ngen pre lv && ih (lv.1 :: pre))

@[expose] noncomputable def stabLowK (n w : Nat) (G : Nat → Nat) (ngen : Nat)
    (L : List (Nat × List Nat × List (List Nat) × List Rec)) : Bool :=
  levelsK n w G ngen L []

@[expose] noncomputable def maskK (R : List Rec) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun r _ ih => Nat.lor (Nat.shiftLeft (nat_lit 1) r.1) ih) R

@[expose] noncomputable def oddOrbK (n w : Nat) (D : Nat → Nat) (ngen x OM : Nat)
    (R : List Rec) : Bool :=
  pointOrbK n w D ngen x R && Nat.beq (maskK R) OM &&
    allN ngen (fun k => allL (fun y => Nat.testBit OM (pg w (mask w) (D k) y))
      (R.map Prod.fst)) &&
    Nat.beq (Nat.land R.length (nat_lit 1)) (nat_lit 1)

end CFSG.KC.PCent

end
