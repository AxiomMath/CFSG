module

public import Certificates.Data.Kernel.WrTwin
public import Certificates.Data.GH74.AE117

public noncomputable section

namespace CFSG.KC.WrPack

open CFSG.KC.WrTwin CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

@[expose] def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun m _ => k (Nat.succ m)) y

@[expose] def pmK (m : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => 0)
    (fun _ ih x y => Nat.add (Nat.land (Nat.shiftRight x (Nat.mul 4 (Nat.land y 15))) 15)
      (Nat.mul 16 (ih x (Nat.shiftRight y 4)))) m

@[expose] def pm (n x y : Nat) : Nat := pmK (2 * n) x y

@[expose] def lvl {n : Nat} (σ : Equiv.Perm (Fin n)) : Nat × Nat :=
  (enc (ofPerm σ), enc (ofPerm σ)⁻¹)

@[expose] def pairMul (n : Nat) (a b : Nat × Nat) : Nat × Nat := (pm n a.1 b.1, pm n b.2 a.2)

@[expose] def prods (n e : Nat) : List (List (Nat × Nat)) → List (Nat × Nat)
  | [] => [(e, e)]
  | E :: L => E.flatMap fun a => (prods n e L).map (pairMul n a)

@[expose] def vecL {n : Nat} (l : List (ZMod 2)) : Fin n → ZMod 2 := fun i => l.getD i.val 0

@[expose] def allL : Nat → List (List (ZMod 2))
  | 0 => [[]]
  | n + 1 => (allL n).flatMap fun l => [0 :: l, 1 :: l]

@[expose] def Vall (n : Nat) : List Nat := (allL n).map fun l => enc (ofVec (vecL (n := n) l))

@[expose] def VevenW (n : Nat) : List (Wr n) :=
  ((allL n).filter fun l => decide (∑ i, vecL (n := n) l i = 0)).map fun l => ofVec (vecL l)

@[expose] def Veven (n : Nat) : List Nat := (VevenW n).map enc

@[expose] def eqPiP (n pp x y : Nat) : Bool := Nat.beq x y || Nat.beq x (pm n y pp)

@[expose] def inModPi (n pp x : Nat) (B : List Nat) : Bool := B.any (eqPiP n pp x)

@[expose] def samePerm (n p q : Nat) : Bool :=
  (List.range n).all fun i => Nat.beq (nib p (2 * i) / 2) (nib q (2 * i) / 2)

@[expose] def centOK (n pp : Nat) (G : List Nat) (P : List (Nat × Nat)) (V C : List Nat) : Bool :=
  P.all fun t => !(G.all fun s => samePerm n (pm n t.1 s) (pm n s t.1)) ||
    V.all fun v => let x := pm n v t.1
      !(G.all fun s => eqPiP n pp (pm n s x) (pm n x s)) || inModPi n pp x C

@[expose] def sqOK (n pp : Nat) (G : List Nat) (P : List (Nat × Nat)) (V Y : List Nat) : Bool :=
  P.all fun t => (strictB (pm n t.1 t.1) fun t2 => strictB (pm n t2 t2) fun t4 =>
    !(G.all fun s => samePerm n (pm n t4 s) (pm n s t4))) || V.all fun v =>
    strictB (pm n v t.1) fun c => strictB (pm n c c) fun c2 => strictB (pm n c2 c2) fun c4 =>
    !(G.all fun s => eqPiP n pp (pm n c4 s) (pm n s c4)) ||
      Y.any fun y => eqPiP n pp (pm n c2 y) (pm n y c2)

@[expose] def inPiP (e pp x : Nat) : Bool := Nat.beq x e || Nat.beq x pp

@[expose] def ord4P (n e pp x : Nat) : Bool :=
  strictB (pm n x x) fun x2 => !inPiP e pp x2 && inPiP e pp (pm n x2 x2)

@[expose] def q8P (n e pp x y : Nat) : Bool :=
  strictB (pm n x x) fun x2 => strictB (pm n x y) fun xy =>
    ord4P n e pp x && eqPiP n pp (pm n y y) x2 && eqPiP n pp (pm n xy xy) x2 && !eqPiP n pp y x &&
      !eqPiP n pp y (pm n x2 x)

@[expose] def q8OK (n e pp : Nat) (P : List (Nat × Nat)) (V : List Nat) (M : List (List Nat)) :
    Bool :=
  P.all fun t => V.all fun v => strictB (pm n v t.1) fun x =>
    !ord4P n e pp x || strictB (pm n x x) fun x2 => P.all fun u =>
      (strictB (pm n x u.1) fun xu =>
        !(samePerm n (pm n u.1 u.1) x2 && samePerm n (pm n xu xu) x2)) ||
      V.all fun w => strictB (pm n w u.1) fun y =>
        !q8P n e pp x y ||
          M.any fun m => m.any (fun a => eqPiP n pp a x) && m.any (fun a => eqPiP n pp a y)

end CFSG.KC.WrPack

end
