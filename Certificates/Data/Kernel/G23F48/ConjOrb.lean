module

public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.G23F48

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def evPN (n w : Nat) (LP LPI : Nat → Nat) : List (Nat × Bool) → Nat :=
  List.rec (motive := fun _ => Nat) (pidn n w) fun l _ ih =>
    pcomp n w (mask w) (Bool.rec (motive := fun _ => Nat) (LPI l.1) (LP l.1) l.2) ih

@[expose] noncomputable def reachP (n w p : Nat) (gs : List Nat) (T : List (Nat × Nat × Nat)) :
    Bool :=
  (T.getD 0 (0, 0, 0)).1 == p && decide (p < n) &&
    (List.range T.length).all fun i =>
      decide ((T.getD i (0, 0, 0)).1 < n) &&
        (i == 0 || decide ((T.getD i (0, 0, 0)).2.1 < i) &&
          decide ((T.getD i (0, 0, 0)).2.2 < gs.length) &&
          pg w (mask w) (gs.getD (T.getD i (0, 0, 0)).2.2 0)
              (T.getD (T.getD i (0, 0, 0)).2.1 (0, 0, 0)).1 == (T.getD i (0, 0, 0)).1)

@[expose] def coverP (T : List (Nat × Nat × Nat)) (lo m : Nat) : Bool :=
  (List.range m).all fun p => (T.map Prod.fst).contains (lo + p)

@[expose] noncomputable def forceL {α : Type} (y : Nat) (k : Nat → α) : α :=
  Nat.rec (motive := fun _ => α) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def pconj (n w g gi x : Nat) : Nat :=
  pcomp n w (mask w) (pcomp n w (mask w) g x) gi

@[expose] noncomputable def ckey (n w : Nat) (v : Nat × Nat) : Nat :=
  v.1 + v.2 + pcomp n w (mask w) v.1 v.2

@[expose] noncomputable def ckids (n w md : Nat) (G GI : List Nat) (v : Nat × Nat) :
    List Nat → (List (Nat × Nat) → Nat → Nat → Bool) → List (Nat × Nat) → Nat → Nat → Bool :=
  List.rec
    (motive := fun _ => (List (Nat × Nat) → Nat → Nat → Bool) → List (Nat × Nat) → Nat → Nat → Bool)
    (fun k B M c => k B M c)
    (fun s _ ih k B M c => Nat.blt s G.length &&
      forceL (pconj n w (G.getD s 0) (GI.getD s 0) v.1) fun x =>
        forceL (pconj n w (G.getD s 0) (GI.getD s 0) v.2) fun y =>
          forceL (Nat.mod (ckey n w (x, y)) md) fun r =>
            !hasBit M r &&
              forceL (Nat.lor M (Nat.shiftLeft (nat_lit 1) r)) fun M' =>
                ih k ((x, y) :: B) M' (Nat.succ c))

@[expose] noncomputable def crun (n w md N : Nat) (G GI : List Nat) :
    List (List Nat) → List (Nat × Nat) → List (Nat × Nat) → Nat → Nat → Bool :=
  List.rec (motive := fun _ => List (Nat × Nat) → List (Nat × Nat) → Nat → Nat → Bool)
    (fun F B _ c => F.isEmpty && B.isEmpty && Nat.beq c N)
    (fun cs _ ih F B M c =>
      List.rec (motive := fun _ => Bool)
        (List.rec (motive := fun _ => Bool) false
          (fun v F' _ => ckids n w md G GI v cs (fun B' M' c' => ih F' B' M' c') [] M c)
          B.reverse)
        (fun v F' _ => ckids n w md G GI v cs (fun B' M' c' => ih F' B' M' c') B M c) F)

@[expose] noncomputable def conjQ (n w md : Nat) (G GI : List Nat) (a b : Nat)
    (C : List (List Nat)) (N : Nat) : Bool :=
  forceL (Nat.mod (ckey n w (a, b)) md) fun r =>
    crun n w md N G GI C [(a, b)] [] (Nat.shiftLeft (nat_lit 1) r) (nat_lit 1)

end CFSG.KC.G23F48

end
