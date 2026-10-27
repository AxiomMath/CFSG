module

public import Certificates.Data.Kernel.WrPack

public noncomputable section

namespace CFSG.KC.WrPackX

open CFSG.KC.WrTwin CFSG.KC.WrPack

@[expose] def allPF (n : Nat) (P : List (Nat × Nat)) (V : List Nat) (g : Nat → Bool)
    (f : Nat → Nat → Bool) : Bool :=
  P.all fun t => g t.1 || V.all fun v =>
    strictB (pm n v t.1) fun x => strictB (pm n t.2 v) fun xi => f x xi

@[expose] def wx (n : Nat) (w : (Nat × Nat) × Nat) : Nat := pm n w.2 w.1.1

@[expose] def wxi (n : Nat) (w : (Nat × Nat) × Nat) : Nat := pm n w.1.2 w.2

@[expose] def okW (P : List (Nat × Nat)) (V : List Nat) (w : (Nat × Nat) × Nat) : Bool :=
  P.any (fun s => Nat.beq s.1 w.1.1 && Nat.beq s.2 w.1.2) && V.any (Nat.beq w.2)

@[expose] def cj (n x w wi : Nat) : Nat := pm n (pm n w x) wi

@[expose] def memB (B : List Nat) (x : Nat) : Bool := B.any (Nat.beq x)

@[expose] def dbl (n pp : Nat) (B : List Nat) : List Nat := B ++ B.map fun y => pm n y pp

@[expose] def pw (n e : Nat) (k : Nat) (x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) e (fun _ acc => pm n acc x) k

@[expose] def twinP (n pp : Nat) (A B : List Nat) : Bool :=
  A.all fun m => B.all fun m' => eqPiP n pp (pm n m m') (pm n m' m)

@[expose] def prodLP (n : Nat) (A B : List Nat) : List Nat :=
  A.flatMap fun m => B.map fun m' => pm n m m'

@[expose] def inv18P (n e pp : Nat) (Pl : List Nat) (z x : Nat) : Bool :=
  Pl.any (fun y => eqPiP n pp x y) && !inPiP e pp x && inPiP e pp (pm n x x) && !eqPiP n pp x z

@[expose] def L18P (n e pp : Nat) (A B : List Nat) : List Nat :=
  (prodLP n A B).filter (inv18P n e pp (prodLP n A B) (A.getD 1 e))

@[expose] def inVP (n e x : Nat) : Bool := samePerm n x e

@[expose] def normGP (n : Nat) (A B P2 : List Nat) (w wi : Nat) : Bool :=
  (A ++ B).all fun g => memB P2 (cj n g w wi)

@[expose] def excOKP (n : Nat) (Ms3 : List (List (Nat × Nat × Bool))) (c ci : Nat) : Bool :=
  Ms3.all fun A => A.all fun m => !m.2.2 ||
    strictB (cj n m.1 c ci) fun y => !(Nat.beq y m.1 || Nat.beq y m.2.1)

@[expose] def a1P (n e : Nat) (L : List Nat) : Bool := L.any (inVP n e) && L.any fun x => !inVP n e x

@[expose] def a2P (n e pp : Nat) (A B P2 L : List Nat) (P : List (Nat × Nat)) (V : List Nat)
    (W : List ((Nat × Nat) × Nat)) : Bool :=
  (W.all fun w => okW P V w &&
      eqPiP n pp (cj n (A.getD 1 e) (wx n w) (wxi n w)) (A.getD 1 e) &&
      normGP n A B P2 (wx n w) (wxi n w)) &&
  [true, false].all fun v => L.any fun x₀ => (inVP n e x₀ == v) && L.all fun x' =>
    (inVP n e x' != v) || W.any fun w => eqPiP n pp (cj n x₀ (wx n w) (wxi n w)) x'

@[expose] def a3P (n e pp : Nat) (Ms : List (List Nat)) (A B : List Nat) (P Q : List (Nat × Nat))
    (V : List Nat) (w : (Nat × Nat) × Nat) : Bool :=
  strictB (cj n (A.getD 1 e) (wx n w) (wxi n w)) fun s =>
    strictB (pm n s (A.getD 1 e)) fun sz =>
    okW P V w && (A.all fun m => B.any fun m' => eqPiP n pp (cj n m s s) m') &&
    (B.all fun m' => A.any fun m => eqPiP n pp (cj n m' s s) m) &&
    !eqPiP n pp s (A.getD 1 e) &&
    (Ms.any fun C => C.any fun m => ord4P n e pp m && eqPiP n pp (pm n sz m) (pm n m sz)) &&
    samePerm n (A.getD 1 e) e &&
    Q.all fun t => !eqPiP n pp (cj n (A.getD 1 e) t.1 t.2) sz

@[expose] def a5P (n e pp a b : Nat) (Ms3 : List (List (Nat × Nat × Bool))) (A B P2 L : List Nat)
    (P : List (Nat × Nat)) (V : List Nat) : Bool :=
  allPF n P V (fun t => strictB (pm n t t) fun t2 =>
      !(samePerm n (pm n t2 a) (pm n a t2) && samePerm n (pm n t2 b) (pm n b t2)))
    fun c ci => strictB (pm n c c) fun c2 =>
      !(eqPiP n pp (pm n c2 a) (pm n a c2) && eqPiP n pp (pm n c2 b) (pm n b c2)) ||
        !normGP n A B P2 c ci || !excOKP n Ms3 c ci ||
        (L.any (fun x => inVP n e x && !eqPiP n pp (cj n x c ci) x) &&
          L.any (fun x => !inVP n e x && !eqPiP n pp (cj n x c ci) x))

end CFSG.KC.WrPackX

end
