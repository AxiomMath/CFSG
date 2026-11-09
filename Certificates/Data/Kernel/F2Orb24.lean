module

public section

namespace CFSG.KC.F2Orb24

inductive BT where
  | nil : BT
  | tip : BT
  | node : BT → BT → BT

@[expose] def ins : Nat → Nat → BT → BT
  | 0, _, _ => .tip
  | d + 1, v, .node l r =>
    if v % 2 = 0 then .node (ins d (v / 2) l) r else .node l (ins d (v / 2) r)
  | d + 1, v, .nil =>
    if v % 2 = 0 then .node (ins d (v / 2) .nil) .nil else .node .nil (ins d (v / 2) .nil)
  | d + 1, v, .tip =>
    if v % 2 = 0 then .node (ins d (v / 2) .nil) .nil else .node .nil (ins d (v / 2) .nil)

@[expose] def mem : Nat → Nat → BT → Bool
  | 0, _, .tip => true
  | 0, _, .nil => false
  | 0, _, .node _ _ => false
  | d + 1, v, .node l r => if v % 2 = 0 then mem d (v / 2) l else mem d (v / 2) r
  | _ + 1, _, .nil => false
  | _ + 1, _, .tip => false

@[expose] def mulC : List Nat → Nat → Nat
  | [], _ => 0
  | c :: cs, v => (if v % 2 = 1 then c else 0) ^^^ mulC cs (v / 2)

@[expose] def bfsK (f g : Nat → Nat) : BT → List (Nat × Bool) → Option BT
  | t, [] => some t
  | t, e :: es =>
    if Nat.blt e.1 16777216 && !mem 24 e.1 t &&
        (Nat.blt (if e.2 then g e.1 else f e.1) 16777216 &&
          mem 24 (if e.2 then g e.1 else f e.1) t) then
      bfsK f g (ins 24 e.1 t) es
    else none

@[expose] def closedK (f g : Nat → Nat) (T : BT) (L : List Nat) : Bool :=
  L.all fun v => Nat.blt (f v) 16777216 && mem 24 (f v) T && Nat.blt (g v) 16777216 &&
    mem 24 (g v) T

@[expose] def sparseOK (cP cQ : List Nat) (root n : Nat) (es : List (Nat × Bool)) : Bool :=
  Nat.beq cP.length 24 && Nat.beq cQ.length 24 && Nat.blt root 16777216 &&
    Nat.beq (es.length + 1) n &&
    match bfsK (mulC cP) (mulC cQ) (ins 24 root .nil) es with
    | none => false
    | some T => closedK (mulC cP) (mulC cQ) T (root :: es.map Prod.fst)

@[expose] noncomputable def lftK (t : BT) : BT := BT.rec (motive := fun _ => BT) BT.nil BT.nil (fun l _ _ _ => l) t

@[expose] noncomputable def rgtK (t : BT) : BT := BT.rec (motive := fun _ => BT) BT.nil BT.nil (fun _ r _ _ => r) t

@[expose] noncomputable def memK (d : Nat) : BT → Nat → Bool :=
  Nat.rec (motive := fun _ => BT → Nat → Bool)
    (fun t _ => BT.rec (motive := fun _ => Bool) false true (fun _ _ _ _ => false) t)
    (fun _ ih t v => BT.rec (motive := fun _ => Bool) false false
      (fun l r _ _ => Bool.rec (motive := fun _ => Bool) (ih r (Nat.shiftRight v (nat_lit 1)))
        (ih l (Nat.shiftRight v (nat_lit 1))) (Nat.beq (Nat.land v (nat_lit 1)) (nat_lit 0))) t) d

@[expose] noncomputable def insK (d : Nat) : Nat → BT → BT :=
  Nat.rec (motive := fun _ => Nat → BT → BT) (fun _ _ => BT.tip)
    (fun _ ih v t => Bool.rec (motive := fun _ => BT)
      (BT.node (lftK t) (ih (Nat.shiftRight v (nat_lit 1)) (rgtK t)))
      (BT.node (ih (Nat.shiftRight v (nat_lit 1)) (lftK t)) (rgtK t)) (Nat.beq (Nat.land v (nat_lit 1)) (nat_lit 0))) d

@[expose] noncomputable def mulCK (l : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun c _ ih v => Nat.xor (Bool.rec (motive := fun _ => Nat) (nat_lit 0) c (Nat.beq (Nat.land v (nat_lit 1)) (nat_lit 1)))
      (ih (Nat.shiftRight v (nat_lit 1)))) l

@[expose] noncomputable def stepOK (v w : Nat) (t : BT) : Bool :=
  Nat.blt v (nat_lit 16777216) && !memK (nat_lit 24) t v && (Nat.blt w (nat_lit 16777216) && memK (nat_lit 24) t w)

@[expose] noncomputable def bfsKK (f g : Nat → Nat) (es : List (Nat × Bool)) : BT → Option BT :=
  List.rec (motive := fun _ => BT → Option BT) (fun t => some t)
    (fun e _ ih t => Prod.rec (motive := fun _ => Option BT) (fun v b =>
      Bool.rec (motive := fun _ => Option BT) none (ih (insK (nat_lit 24) v t))
        (stepOK v (Bool.rec (motive := fun _ => Nat) (f v) (g v) b) t)) e) es

@[expose] noncomputable def closedKK (f g : Nat → Nat) (T : BT) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun v _ ih => Nat.blt (f v) (nat_lit 16777216) && memK (nat_lit 24) T (f v) && Nat.blt (g v) (nat_lit 16777216) &&
      memK (nat_lit 24) T (g v) && ih) L

@[expose] noncomputable def sparseK (cP cQ : List Nat) (root n : Nat) (es : List (Nat × Bool)) :
    Bool :=
  Nat.beq cP.length 24 && Nat.beq cQ.length 24 && Nat.blt root 16777216 &&
    Nat.beq (es.length + 1) n &&
    Option.rec (motive := fun _ => Bool) false
      (fun T => closedKK (mulCK cP) (mulCK cQ) T (root :: es.map Prod.fst))
      (bfsKK (mulCK cP) (mulCK cQ) es (insK 24 root .nil))

end CFSG.KC.F2Orb24

end
