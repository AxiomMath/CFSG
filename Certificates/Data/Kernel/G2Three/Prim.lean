module

public import Certificates.Data.Kernel.G2Three.K7b

public section

namespace CFSG.KD.G2Three

open CFSG.KC.Ord CFSG.KC.Loop

@[expose] noncomputable def TOP : Nat := Nat.shiftLeft 1 392

@[expose] noncomputable def canK (x : Nat) : Bool :=
  Nat.blt x TOP && Nat.beq (Nat.land x (Nat.shiftRight x 196)) 0

@[expose] noncomputable def actK (A B P : Nat) : Nat := MUL (MUL A P) B

@[expose] noncomputable def wA (GA : Nat → Nat) (w : List Nat) : Nat :=
  w.foldr (fun k acc => MUL (GA k) acc) ONE

@[expose] noncomputable def wB (GB : Nat → Nat) (w : List Nat) : Nat :=
  w.foldl (fun acc k => MUL (GB k) acc) ONE

@[expose] def ltK (w : List Nat) : Bool := w.all fun k => Nat.blt k 8

@[expose] noncomputable def decW (L c : Nat) : List Nat :=
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun _ ih c => Nat.mod c 8 :: ih (Nat.div c 8)) L c

@[expose] noncomputable def clStep (X CA CB IMG : Nat → Nat) (N i x k : Nat) : Bool :=
  Nat.blt (IMG (Nat.add (Nat.mul 4 i) k)) N &&
    Nat.beq (X (IMG (Nat.add (Nat.mul 4 i) k))) (actK (CA k) (CB k) x)

@[expose] noncomputable def closK (X CA CB IMG : Nat → Nat) (N c S hi : Nat) : Bool :=
  allBelow S hi fun j => (fun i => cond (Nat.blt i N)
    ((fun x => clStep X CA CB IMG N i x 0 && clStep X CA CB IMG N i x 1 &&
      clStep X CA CB IMG N i x 2 && clStep X CA CB IMG N i x 3) (X i)) true)
    (Nat.add (Nat.mul c S) j)

@[expose] noncomputable def forStep (X HA HB LAB HP HS ROOTS : Nat → Nat) (nh m i : Nat) : Bool :=
  canK (X i) && Nat.blt (LAB i) m &&
    cond (Nat.beq (ROOTS (LAB i)) i) true
      (Nat.blt (HP i) i && Nat.blt (HS i) nh && Nat.beq (LAB (HP i)) (LAB i) &&
        Nat.beq (X i) (actK (HA (HS i)) (HB (HS i)) (X (HP i))))

@[expose] noncomputable def forK (X HA HB LAB HP HS ROOTS : Nat → Nat) (N nh m c S hi : Nat) : Bool :=
  allBelow S hi fun j => (fun i => cond (Nat.blt i N) (forStep X HA HB LAB HP HS ROOTS nh m i) true)
    (Nat.add (Nat.mul c S) j)

@[expose] noncomputable def hK (X0 : Nat) (GA GB HA HB : Nat → Nat) (W : Nat → List Nat) (nh : Nat) :
    Bool :=
  allBelow nh 1 fun s => ltK (W s) && Nat.beq (HA s) (wA GA (W s)) &&
    Nat.beq (HB s) (wB GB (W s)) && Nat.beq (actK (HA s) (HB s) X0) X0

@[expose] noncomputable def rootK (X GA GB RA RB RL RC ROOTS : Nat → Nat) (N m hi : Nat) : Bool :=
  Nat.beq (ROOTS 0) 0 && allBelow m hi fun q => cond (Nat.beq q 0) true
    (Nat.blt (ROOTS q) N && Nat.beq (RA q) (wA GA (decW (RL q) (RC q))) &&
      Nat.beq (RB q) (wB GB (decW (RL q) (RC q))) &&
      Nat.beq (actK (RA q) (RB q) (X 0)) (X (ROOTS q)))

@[expose] noncomputable def trStep (X RA RB LAB TP TD EU EV : Nat → Nat) (N m t : Nat) : Bool :=
  (fun j q => cond (Nat.beq j 0 || Nat.beq q 0) true
    (Nat.blt (TP t) m && Nat.blt (TD (Nat.add (Nat.mul j m) (TP t))) (TD t) &&
      Nat.blt (EU t) N && Nat.blt (EV t) N && Nat.beq (LAB (EU t)) (TP t) &&
      Nat.beq (LAB (EV t)) q && Nat.beq (X (EV t)) (actK (RA j) (RB j) (X (EU t)))))
    (Nat.div t m) (Nat.mod t m)

@[expose] noncomputable def trK (X RA RB LAB TP TD EU EV : Nat → Nat) (N m hi : Nat) : Bool :=
  allBelow (Nat.mul m m) hi (trStep X RA RB LAB TP TD EU EV N m)

@[expose] def inv8 (k : Nat) : Nat := cond (Nat.beq (Nat.mod k 2) 0) (Nat.succ k) (Nat.pred k)

@[expose] noncomputable def twG (G : Nat → Nat) (σ : List Nat) (k : Nat) : Nat := G (inv8 (σ.getD k 0))

@[expose] noncomputable def cK (GA GB CA CB : Nat → Nat) : Bool :=
  allBelow 4 1 fun k => Nat.beq (CA k) (GA (Nat.mul 2 k)) && Nat.beq (CB k) (GB (Nat.mul 2 k))

@[expose] noncomputable def ntK (X CA CB : Nat → Nat) : Bool :=
  !(Nat.beq (actK (CA 0) (CB 0) (X 0)) (X 0) && Nat.beq (actK (CA 1) (CB 1) (X 0)) (X 0) &&
    Nat.beq (actK (CA 2) (CB 2) (X 0)) (X 0) && Nat.beq (actK (CA 3) (CB 3) (X 0)) (X 0))

end CFSG.KD.G2Three

end
