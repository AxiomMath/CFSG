module

public import Certificates.Data.Kernel.Fi23R.Defs

public section

namespace CFSG.KC.Fi23Cov

@[expose] noncomputable def chW (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun l _ ih => Nat.blt (nat_lit 51) l && Nat.blt l (nat_lit 76) && ih) w

@[expose] noncomputable def chA (W : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun w _ ih => chW w && ih) W

@[expose] noncomputable def nthW (l : List (List Nat)) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun a _ ih j => Nat.rec (motive := fun _ => List Nat) a (fun k _ => ih k) j) l i

@[expose] noncomputable def catW (W : List (List Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun w _ ih => w ++ ih) W

@[expose] noncomputable def expC (M : List (List Nat)) (c : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun k _ ih => nthW M k ++ ih) c

@[expose] noncomputable def lenLe (W : List (List Nat)) (n : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ _ ih n => Nat.rec (motive := fun _ => Bool) false (fun m _ => ih m) n) W n

@[expose] noncomputable def repW (w : List Nat) (p : Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) [] (fun _ ih => w ++ ih) p

@[expose] noncomputable def cm (E : List Nat → List Nat → Bool) (u v : List Nat) : Bool :=
  E (u ++ v) (v ++ u)

@[expose] noncomputable def fHead (E : List Nat → List Nat → Bool) (u₁ u₂ h : List Nat)
    (M : List (List Nat)) (nM : Nat) (Ra : List (List Nat)) (na : Nat) (Rb : List (List Nat))
    (nb : Nat) : Bool :=
  lenLe M nM && lenLe Ra na && lenLe Rb nb && chW u₁ && chW u₂ && chW h && chA M && chA Ra &&
    chA Rb && E (repW u₁ 5) [] && E (repW u₂ 5) [] && !E u₁ [] && cm E u₁ u₂ &&
    E (h ++ u₁) (u₂ ++ h)

@[expose] noncomputable def fLet (E : List Nat → List Nat → Bool) (u₁ u₂ : List Nat)
    (M : List (List Nat)) (j : Nat) : Bool :=
  E (nthW M (2 * j) ++ nthW M (2 * j + 1)) [] &&
    (cm E (nthW M (2 * j)) u₁ || cm E (nthW M (2 * j)) u₂)

@[expose] noncomputable def stOK (E : List Nat → List Nat → Bool) (M C R : List (List Nat))
    (k : Nat) : Bool :=
  E (expC M (nthW C k)) (nthW R k)

@[expose] noncomputable def prOK (E : List Nat → List Nat → Bool) (R : List (List Nat))
    (t : List Nat) : Bool :=
  E (catW R) t

@[expose] def t3W : List (List Nat) :=
  [[3, 2], [68, 68, 70, 72, 65, 70, 74, 61, 66, 60, 67, 56, 59, 71, 65, 52, 55, 59, 71],
    [1, 2, 5, 4], [1, 6, 0, 7, 3, 5]]

@[expose] noncomputable def tOK (E : List Nat → List Nat → Bool) (T : List (List Nat)) (i : Nat) :
    Bool :=
  chW (nthW T i) && E (nthW T i) (nthW t3W i) && E (repW (nthW T i) 3) []

@[expose] noncomputable def genOK (E : List Nat → List Nat → Bool) : Bool :=
  E [39, 39] [] && E [40, 41] []

@[expose] noncomputable def link (E : List Nat → List Nat → Bool) (x z h a ai : List Nat) : Bool :=
  E (h ++ x) (z ++ h) && cm E x z && cm E z (a ++ x ++ ai)

@[expose] noncomputable def ctlA (E : List Nat → List Nat → Bool) (t g x z₁ h₁ z₂ h₂ : List Nat) :
    Bool :=
  chW g && chW x && chW z₁ && chW h₁ && chW z₂ && chW h₂ && E (repW x 3) [] &&
    E (g ++ t) (x ++ g) && link E x z₁ h₁ [39] [39] && link E x z₂ h₂ [40] [41]

@[expose] noncomputable def ctlB (E : List Nat → List Nat → Bool) (t g x : List Nat) : Bool :=
  chW g && chW x && E (repW x 3) [] && E (g ++ t) (x ++ g) && cm E x [40] &&
    cm E x ([39] ++ x ++ [39])

@[expose] noncomputable def clH (E : List Nat → List Nat → Bool) (t y₁ y₂ g₁ g₂ s : List Nat)
    (M : List (List Nat)) (nM : Nat) (R : List (List Nat)) (nR : Nat) : Bool :=
  lenLe M nM && lenLe R nR && chW y₁ && chW y₂ && chW g₁ && chW g₂ && chA M && chA R &&
    E (repW y₁ 3) [] && E (repW y₂ 3) [] && E (g₁ ++ t) (y₁ ++ g₁) && E (g₂ ++ t) (y₂ ++ g₂) &&
    cm E y₁ y₂ && cm E y₁ s

@[expose] noncomputable def clL (E : List Nat → List Nat → Bool) (y₁ y₂ : List Nat) (n : Nat)
    (M : List (List Nat)) (j : Nat) : Bool :=
  E (nthW M (2 * j) ++ nthW M (2 * j + 1)) [] &&
    cm E (nthW M (2 * j)) (cond (Nat.blt j n) y₁ y₂)

end CFSG.KC.Fi23Cov

end
