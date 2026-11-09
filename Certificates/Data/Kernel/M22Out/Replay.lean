module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.TabCheck

public section

namespace CFSG.KC.M22Out

open CFSG.EvenSporadicStandard.M22Std.TabCheck

@[expose] noncomputable def getK (l : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun a _ r i => Nat.rec (motive := fun _ => Nat) a (fun j _ => r j) i) l

@[expose] noncomputable def getLK {α : Type} (l : List α) (d : α) : Nat → α :=
  List.rec (motive := fun _ => Nat → α) (fun _ => d)
    (fun a _ r i => Nat.rec (motive := fun _ => α) a (fun j _ => r j) i) l

@[expose] noncomputable def tmulK (s t : Tab) : Tab :=
  List.rec (motive := fun _ => Tab) [] (fun j _ r => getK s j :: r) t

@[expose] noncomputable def eqK (a : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun b => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) b)
    (fun x _ r b => List.rec (motive := fun _ => Bool) false
      (fun y bs _ => Bool.rec false (r bs) (Nat.beq x y)) b) a

@[expose] noncomputable def commGoK (s t a : Tab) : Tab → Bool :=
  List.rec (motive := fun _ => Tab → Bool)
    (fun b => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) b)
    (fun x _ r b => List.rec (motive := fun _ => Bool) false
      (fun y bs _ => Bool.rec false (r bs) (Nat.beq (getK s x) (getK t y))) b) a

@[expose] noncomputable def allK {α : Type} (p : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ r => Bool.rec false r (p a)) l

@[expose] noncomputable def validGo (t : Tab) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun n => Nat.beq n 22)
    (fun a _ r n => Bool.rec false (r (Nat.succ n)) (Nat.blt a 22)) t

@[expose] noncomputable def validK (t : Tab) : Bool := validGo t 0

@[expose] noncomputable def isInvK (t : Tab) : Bool := Bool.rec (eqK (tmulK t t) idTab) false (eqK t idTab)

@[expose] noncomputable def memK (t : Tab) (L : List Tab) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ r => Bool.rec r true (eqK t a)) L

@[expose] noncomputable def keyGo (t : Tab) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun x _ r acc => r (Nat.add (Nat.mul acc 22) x)) t

@[expose] noncomputable def keyK (t : Tab) : Nat := keyGo t 0

@[expose] noncomputable def filtEqK (p : Tab → Bool) (L : List Tab) : List Tab → Bool :=
  List.rec (motive := fun _ => List Tab → Bool)
    (fun Is => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) Is)
    (fun t _ r Is => Bool.rec (r Is)
      (List.rec (motive := fun _ => Bool) false (fun u us _ => Bool.rec false (r us) (eqK t u)) Is)
      (p t)) L

@[expose] noncomputable def strictK {β : Sort _} (y : Nat) (k : Nat → β) : β :=
  Nat.rec (motive := fun _ => β) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def countK (p : Tab → Bool) (l : List Tab) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun a _ r acc => strictK (Bool.rec acc (Nat.succ acc) (p a)) r) l

@[expose] noncomputable def centK (L₁ L₂ : List Tab) (t : Tab) : Nat :=
  countK (fun l => commGoK l t t l) L₂ (countK (fun l => commGoK l t t l) L₁ 0)

@[expose] noncomputable def dropK {α : Type} (L : List α) (d : Nat) : List α :=
  Nat.rec (motive := fun _ => List α) L (fun _ r => List.tail r) d

@[expose] noncomputable def centWK (t : Tab) : List Nat → List Tab → Bool :=
  List.rec (motive := fun _ => List Tab → Bool) (fun _ => true)
    (fun d _ ih L => List.rec (motive := fun _ => Bool) false
      (fun x L' _ => Bool.rec false (ih L') (commGoK x t t x)) (dropK L d))

@[expose] noncomputable def fixK (F : List Tab) (t : Tab) : Nat :=
  countK (fun x => commGoK t x x t) F 0

@[expose] noncomputable def laneW (w m P k : Nat) : Nat :=
  Nat.land (Nat.shiftRight P (Nat.mul w k)) m

@[expose] noncomputable def packL (b : Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun a _ r => Nat.add a (Nat.mul b r)) l

@[expose] noncomputable def packT (t : Tab) : Nat := packL (nat_lit 32) t

@[expose] noncomputable def packTs (T : List Tab) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun t _ r => Nat.add (packT t) (Nat.mul (nat_lit 1298074214633706907132624082305024) r)) T

@[expose] noncomputable def encW (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 1) (fun i _ r => Nat.add i (Nat.mul (nat_lit 2) r)) w

@[expose] noncomputable def packW (W : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun w _ r => Nat.add (encW w) (Nat.mul (nat_lit 131072) r)) W

@[expose] noncomputable def tabAt (TP k : Nat) : Nat :=
  laneW (nat_lit 110) (nat_lit 1298074214633706907132624082305023) TP k

@[expose] noncomputable def wordAt (WP k : Nat) : Nat := laneW (nat_lit 17) (nat_lit 131071) WP k

@[expose] noncomputable def stepK (TP WP : Nat) (g t : Tab) (i e k q c : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0)
    (Bool.rec (motive := fun _ => Nat)
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) c (Nat.blt k c))
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.succ c)
        (Nat.beq (wordAt WP c) (Nat.add i (Nat.mul (nat_lit 2) e))))
      (Nat.beq k c))
    (and (Nat.blt q c) (Nat.beq (packT (tmulK g t)) (tabAt TP k)))

@[expose] noncomputable def replayK (TP WP : Nat) (g₀ g₁ : Tab) (T : List Tab) :
    List Nat → List (List Nat) → Nat → Nat → Nat :=
  List.rec (motive := fun _ => List Nat → List (List Nat) → Nat → Nat → Nat)
    (fun _ _ _ c => c)
    (fun t _ ih E KK q c =>
      strictK (stepK TP WP g₁ t (nat_lit 1) (E.headD 0) ((KK.headD []).getD 1 0) q
        (strictK (stepK TP WP g₀ t (nat_lit 0) (E.headD 0) ((KK.headD []).getD 0 0) q c)
          fun c' => c'))
        fun c'' => ih E.tail KK.tail (Nat.succ q) c'')
    T

@[expose] noncomputable def packKeys (L : List Tab) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun t _ r => Nat.add (keyK t)
      (Nat.mul (nat_lit 1267650600228229401496703205376) r)) L

@[expose] noncomputable def keysK (KP n : Nat) (σ : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun j _ ih prev =>
      strictK (laneW (nat_lit 100) (nat_lit 1267650600228229401496703205375) KP j) fun kj =>
        and (and (Nat.blt j n) (Nat.blt prev kj)) (ih kj))
    σ

@[expose] noncomputable def mapEqK (f : Tab → Tab) (T : List Tab) : List Tab → Bool :=
  List.rec (motive := fun _ => List Tab → Bool) (fun us => Nat.beq us.length 0)
    (fun t _ ih us => and (Nat.beq (packT (f t)) (packT (us.headD []))) (ih us.tail)) T

@[expose] def conjT (g gi t : Tab) : Tab := tmul (tmul g t) gi

@[expose] noncomputable def conjTreeK (gs gis I : List Tab) (PR : List (Nat × Nat × Nat)) :
    List (Nat × Nat × Nat) → List Tab → Bool :=
  List.rec (motive := fun _ => List Tab → Bool) (fun _ => true)
    (fun e _ ih Is =>
      and
        (Bool.rec (motive := fun _ => Bool)
          (and (and (Nat.blt e.2.1 3) (Nat.blt (getLK PR (0, 0, 0) e.1).2.2 e.2.2))
            (eqK (tmulK (tmulK (gs.getD e.2.1 idTab) (getLK I idTab e.1)) (gis.getD e.2.1 idTab))
              (Is.headD idTab)))
          (Nat.beq e.2.2 0) (Nat.beq e.2.1 3))
        (ih Is.tail))

end CFSG.KC.M22Out
