module

public section

namespace CFSG.KC.SporCov

@[expose] noncomputable def chW (L : Nat → Bool) (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun l _ ih => L l && ih) w

@[expose] noncomputable def chA (L : Nat → Bool) (W : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun w _ ih => chW L w && ih) W

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

@[expose] noncomputable def cjOK (E : List Nat → List Nat → Bool) (t g x : List Nat) : Bool :=
  E (g ++ t) (x ++ g)

@[expose] noncomputable def genOK (E : List Nat → List Nat → Bool) (L : Nat → Bool) (a ai b bi : List Nat) :
    Bool :=
  chW L a && chW L ai && chW L b && chW L bi && E (a ++ ai) [] && E (b ++ bi) []

@[expose] noncomputable def repOK (E : List Nat → List Nat → Bool) (L : Nat → Bool) (p : Nat)
    (T : List (List Nat)) (i : Nat) (r : List Nat) : Bool :=
  chW L (nthW T i) && chW L r && E (nthW T i) r && E (repW (nthW T i) p) []

@[expose] noncomputable def link (E : List Nat → List Nat → Bool) (x z h c ci : List Nat) : Bool :=
  E (h ++ x) (z ++ h) && cm E x z && cm E z (c ++ x ++ ci)

@[expose] noncomputable def ctlA (E : List Nat → List Nat → Bool) (L : Nat → Bool) (p : Nat)
    (t g x z₁ h₁ z₂ h₂ a ai b bi : List Nat) : Bool :=
  chW L g && chW L x && chW L z₁ && chW L h₁ && chW L z₂ && chW L h₂ && E (repW x p) [] &&
    cjOK E t g x && link E x z₁ h₁ a ai && link E x z₂ h₂ b bi

@[expose] noncomputable def ctlB (E : List Nat → List Nat → Bool) (L : Nat → Bool) (p : Nat)
    (t g x y h a b : List Nat) : Bool :=
  chW L g && chW L x && chW L y && chW L h && E (repW x p) [] && cjOK E t g x && cm E x b &&
    cm E x y && E (h ++ x) (y ++ h) && (cm E y a || E h a)

@[expose] noncomputable def clH (E : List Nat → List Nat → Bool) (L : Nat → Bool) (p : Nat)
    (t y₁ y₂ g₁ g₂ : List Nat) (M : List (List Nat)) (nL : Nat) : Bool :=
  lenLe M (2 * nL) && chW L y₁ && chW L y₂ && chW L g₁ && chW L g₂ && chA L M &&
    E (repW y₁ p) [] && E (repW y₂ p) [] && cjOK E t g₁ y₁ && cjOK E t g₂ y₂ && cm E y₁ y₂

@[expose] noncomputable def clL (E : List Nat → List Nat → Bool) (y₁ y₂ : List Nat) (n : Nat)
    (M : List (List Nat)) (j : Nat) : Bool :=
  E (nthW M (2 * j) ++ nthW M (2 * j + 1)) [] &&
    cm E (nthW M (2 * j)) (cond (Nat.blt j n) y₁ y₂)

@[expose] noncomputable def stH (L : Nat → Bool) (R : List (List Nat)) (nR : Nat) : Bool :=
  lenLe R nR && chA L R

@[expose] noncomputable def stOK (E : List Nat → List Nat → Bool) (M C R : List (List Nat)) (k : Nat) : Bool :=
  E (expC M (nthW C k)) (nthW R k)

@[expose] noncomputable def prOK (E : List Nat → List Nat → Bool) (L : Nat → Bool) (R : List (List Nat))
    (o : List Nat) : Bool :=
  chW L o && E (catW R) o

@[expose] noncomputable def neOK (E : List Nat → List Nat → Bool) (u : List Nat) : Bool :=
  !E u []

@[expose] noncomputable def p3OK (E : List Nat → List Nat → Bool) (L : Nat → Bool) (p : Nat)
    (g₁ g₂ z : List Nat) (e₁ e₂ : Nat) : Bool :=
  chW L g₁ && chW L g₂ && chW L z && neOK E z && E (repW z p) [] && cm E z g₁ && cm E z g₂ &&
    E (g₂ ++ g₁) (g₁ ++ g₂ ++ z) && E (repW g₁ p) (repW z e₁) && E (repW g₂ p) (repW z e₂)

@[expose] noncomputable def lineOK (E : List Nat → List Nat → Bool) (L : Nat → Bool) (g₁ g₂ : List Nat)
    (i : Nat) (t : List Nat) : Bool :=
  chW L t && E t (repW g₂ i ++ g₁)

end CFSG.KC.SporCov

end
