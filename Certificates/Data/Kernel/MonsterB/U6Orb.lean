module

public import CFSG.Certificates.Kernel.Lie.CT.Core
public import Certificates.Data.Kernel.MonsterB.BfsReplay

public section

namespace CFSG.KC.U6Orb

open CFSG.KLie.CT CFSG.KC.Loop

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def packL (w : Nat) (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun x _ ih => Nat.lor x (Nat.shiftLeft ih w)) L

@[expose] noncomputable def mapL {α : Type} (f : α → Nat) (L : List α) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun x _ ih => List.cons (f x) ih) L

@[expose] noncomputable def lenL {α : Type} (L : List α) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def allL {α : Type} (f : α → Bool) (L : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => andB (f x) ih) L

@[expose] noncomputable def boundL (b : Nat) (L : List Nat) : Bool :=
  allL (fun x => Nat.blt x b) L

@[expose] noncomputable def shapeL (n b : Nat) (LL : List (Array Nat)) : Bool :=
  allL (fun L => andB (Nat.beq (lenL L.toList) n) (boundL b L.toList)) LL

@[expose] noncomputable def nodupM (L : List Nat) (M : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih M => andB (notB (bit M x)) (strictB (Nat.lor M (pw2 x)) ih)) L M

@[expose] noncomputable def xorK (n : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun t ih => Nat.xor (f t) ih) n

@[expose] noncomputable def actK (M v : Nat) : Nat :=
  xorK (nat_lit 22) fun t => nIf(bit v t, fget M t (nat_lit 22), nat_lit 0)

@[expose] noncomputable def edgeOK (V RR : Nat) (E : Nat → Nat → Nat) (n ng : Nat) : Bool :=
  allN n fun i => allN ng fun k => andB (Nat.blt (E i k) n)
    (Nat.beq (fget V (E i k) (nat_lit 22)) (actK (fget RR k (nat_lit 484)) (fget V i (nat_lit 22))))

@[expose] noncomputable def edgeLOK (L : List Nat) (R : List (Array Nat)) (D : Nat)
    (Ef : Nat → Nat → Nat → Nat) (n ng : Nat) : Bool :=
  strictB D fun D => strictB (packL (nat_lit 22) L) fun V =>
    strictB (packL (nat_lit 484) (mapL (fun a => packL (nat_lit 22) a.toList) R)) fun RR =>
      edgeOK V RR (Ef D) n ng

@[expose] noncomputable def permTab (n w D i k : Nat) : Nat :=
  fget (fget D k (Nat.mul n w)) i w

@[expose] noncomputable def packP (n w : Nat) (P : List (Array Nat)) : Nat :=
  packL (Nat.mul n w) (mapL (fun a => packL w a.toList) P)

@[expose] noncomputable def tabE (ng w D i k : Nat) : Nat := fget D (Nat.add (Nat.mul i ng) k) w

@[expose] noncomputable def memOK (L : List Nat) (s X wX I wI n m c : Nat) : Bool :=
  strictB (packL (nat_lit 22) L) fun V => strictB X fun X => strictB I fun I => allN m fun j =>
    (fun y => (fun t => andB (Nat.blt t n) (andB (Nat.beq (fget X t wX) y)
      (andB (Nat.blt y (pw2 (nat_lit 22))) (notB (Nat.beq y c))))) (fget I j wI))
      (Nat.xor s (fget V j (nat_lit 22)))

@[expose] noncomputable def sortOK (L : List Nat) (S w n : Nat) : Bool :=
  andB (Nat.beq (lenL L) n) (andB (boundL (pw2 (nat_lit 22)) L)
    (strictB (packL (nat_lit 22) L) fun V => strictB S fun S => allN n fun t =>
      andB (Nat.blt (fget S t w) n) (bIf(Nat.blt (Nat.succ t) n,
        Nat.blt (fget V (fget S t w) (nat_lit 22)) (fget V (fget S (Nat.succ t) w) (nat_lit 22)),
        true))))

@[expose] noncomputable def replayDOK (D : Nat) (Ef : Nat → Nat → Nat → Nat) (ng n : Nat) : Bool :=
  strictB D fun D => CFSG.KC.Bfs.replayOK (Ef D) ng n

end CFSG.KC.U6Orb

end
