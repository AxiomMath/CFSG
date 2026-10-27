module

public import CFSG.Certificates.Kernel.Spor.PackWord

public section

namespace CFSG.KC.M305

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.PEnum

@[expose] noncomputable def m305mul (p q : Nat) : Nat := pcomp 275 9 (mask 9) p q

@[expose] noncomputable def m305id : Nat := pidn 275 9

@[expose] noncomputable def m305all (f : Nat → Bool) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => bAnd(f x, ih)) L

@[expose] noncomputable def m305prod (bs : List Nat) (c : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => m305id)
    (fun b _ ih c => Bool.rec (motive := fun _ => Nat) (ih (Nat.div c 2))
      (m305mul b (ih (Nat.div c 2))) (Nat.beq (Nat.mod c 2) 1)) bs c

@[expose] noncomputable def m305word (S : Nat → Nat) (wd : List Nat) : Nat :=
  wordTabK 275 9 (mask 9) (pidn 275 9) S wd

@[expose] noncomputable def m305words (S : Nat → Nat) (wds : List (List Nat)) (Ts : List Nat) :
    Bool :=
  (List.rec (motive := fun _ => List Nat → Bool)
    (fun Ts => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) Ts)
    (fun wd _ ih Ts => List.rec (motive := fun _ => Bool) false
      (fun T Ts' _ => bAnd(Nat.beq (m305word S wd) T, ih Ts')) Ts)) wds Ts

@[expose] noncomputable def m305basis (bs : List Nat) : Bool :=
  bAnd(m305all (fun b => bAnd(canonK 275 9 (mask 9) (275 * 9) b,
      Nat.beq (m305mul b b) m305id)) bs,
    bAnd(m305all (fun b => m305all (fun b' => Nat.beq (m305mul b b') (m305mul b' b)) bs) bs,
      Nat.rec (motive := fun _ => Bool) true
        (fun c acc => bAnd(bIf(Nat.beq c 0, true,
          bIf(Nat.beq (m305prod bs c) m305id, false, true)), acc)) (Nat.pow 2 (List.length bs))))

@[expose] noncomputable def m305bit (O i : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight O i) 1) 1

@[expose] noncomputable def m305fix (bs : List Nat) (O : Nat) : Bool :=
  allN 275 (fun i => Bool.rec (motive := fun _ => Bool)
    (bIf(m305all (fun b => Nat.beq (pg 9 (mask 9) b i) i) bs, false, true))
    (m305all (fun b => Nat.beq (pg 9 (mask 9) b i) i) bs) (m305bit O i))

@[expose] noncomputable def m305img (O : List Nat) (h : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0
    (fun p _ acc => Nat.lor acc (Nat.shiftLeft 1 (pg 9 (mask 9) h p))) O

@[expose] noncomputable def m305mask (O : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun p _ acc => Nat.lor acc (Nat.shiftLeft 1 p)) O

@[expose] noncomputable def m305dist (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun x xs ih => bAnd(m305all (fun y => bIf(Nat.beq x y, false, true)) xs, ih)) L

@[expose] noncomputable def m305nrm (bs : List Nat) (m : Nat) (cs : List Nat) : Bool :=
  (List.rec (motive := fun _ => List Nat → Bool)
    (fun cs => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) cs)
    (fun b _ ih cs => List.rec (motive := fun _ => Bool) false
      (fun c cs' _ => bAnd(Nat.beq (m305mul m b) (m305mul (m305prod bs c) m), ih cs')) cs)) bs cs

@[expose] noncomputable def m305ord (p k : Nat) : Bool :=
  bAnd(Nat.beq (ppow 275 9 (mask 9) m305id p k) m305id, bIf(Nat.beq p m305id, false, true))

@[expose] noncomputable def m305comm (p q : Nat) : Bool :=
  allN 275 (fun i => Nat.beq (pg 9 (mask 9) p (pg 9 (mask 9) q i))
    (pg 9 (mask 9) q (pg 9 (mask 9) p i)))

@[expose] noncomputable def m305e8 (x t N : Nat) (T : Nat → Nat) : Bool :=
  allN N (fun i => bIf(m305comm x (T i), allN N (fun j => bIf(m305comm x (T j),
    bIf(m305comm (T i) (T j), bIf(Nat.beq (T j) (T i), true, Nat.beq (T j) (m305mul (T i) t)),
      true), true)), true))

@[expose] noncomputable def m305cnt (N : Nat) (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun j acc => Bool.rec (motive := fun _ => Nat) acc
    (Nat.succ acc) (f j)) N

@[expose] noncomputable def m305sq (p : Nat) : Bool := Nat.beq (m305mul p p) m305id

@[expose] noncomputable def m305cls (N : Nat) (T : Nat → Nat) (C : Nat) (bs : List Nat) (r : Nat) :
    Bool :=
  allN N (fun i => bIf(Nat.beq (pg 6 (mask 6) C i) 0, bIf(m305sq (T i), false, true),
    bIf(Nat.blt (pg 6 (mask 6) C i) 17,
      Nat.beq (T i) (m305prod bs (Nat.sub (pg 6 (mask 6) C i) 1)),
    bIf(Nat.blt (pg 6 (mask 6) C i) 33,
      Nat.beq (m305mul (T i) r) (m305mul r (m305prod bs (Nat.sub (pg 6 (mask 6) C i) 17))),
      bAnd(m305sq (T i), Nat.blt (m305cnt N (fun j => bAnd(m305sq (T j), m305comm (T j) (T i))))
        16)))))

@[expose] noncomputable def m305cov (N : Nat) (T : Nat → Nat) (t M : Nat) (U : Nat → Nat)
    (X : Nat) : Bool :=
  allN N (fun i => bIf(m305sq (T i), bIf(Nat.beq (T i) m305id, true, bIf(Nat.beq (T i) t, true,
    bAnd(Nat.blt (pg 8 (mask 8) X i) M, Nat.beq (T i) (U (pg 8 (mask 8) X i))))), true))

@[expose] def oAct : List (Array Nat) := [#[1, 4, 6, 2, 3, 0, 5], #[6, 5, 1, 2, 0, 4, 3]]

@[expose] def sKeys : List Nat := [1, 9, 0]

end CFSG.KC.M305

end
