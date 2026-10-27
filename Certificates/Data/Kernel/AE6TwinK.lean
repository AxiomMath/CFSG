module

public import Certificates.Data.Kernel.WrTwin
public import Certificates.Data.GH74.AE117

public noncomputable section

namespace CFSG.KC.AE6TwinK

open CFSG.KC.WrTwin CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
  Certificates.AE117

@[expose] def pm (x y : Nat) : Nat := pmul 12 x y

@[expose] def lvl (σ : Equiv.Perm (Fin 6)) : Nat × Nat := (enc (ofPerm σ), enc (ofPerm σ)⁻¹)

@[expose] def pairMul (a b : Nat × Nat) : Nat × Nat := (pm a.1 b.1, pm b.2 a.2)

@[expose] def prods (e : Nat) : List (List (Nat × Nat)) → List (Nat × Nat)
  | [] => [(e, e)]
  | E :: L => E.flatMap fun a => (prods e L).map (pairMul a)

@[expose] def vecL (l : List (ZMod 2)) : Fin 6 → ZMod 2 := fun i => l.getD i.val 0

@[expose] def allL : Nat → List (List (ZMod 2))
  | 0 => [[]]
  | n + 1 => (allL n).flatMap fun l => [0 :: l, 1 :: l]

@[expose] def V64 : List Nat := (allL 6).map fun l => enc (ofVec (vecL l))

@[expose] def E32W : List (Wr 6) :=
  ((allL 6).filter fun l => decide (∑ i, vecL l i = 0)).map fun l => ofVec (vecL l)

@[expose] def E32 : List Nat := E32W.map enc

@[expose] def eqPiP (pp x y : Nat) : Bool := Nat.beq x y || Nat.beq x (pm y pp)

@[expose] def inModPi (pp x : Nat) (B : List Nat) : Bool := B.any (eqPiP pp x)

@[expose] def samePerm (p q : Nat) : Bool :=
  (List.range 6).all fun i => Nat.beq (nib p (2 * i) / 2) (nib q (2 * i) / 2)

@[expose] def centOK (pp : Nat) (G : List Nat) (P : List (Nat × Nat)) (V C : List Nat) : Bool :=
  P.all fun t => !(G.all fun s => samePerm (pm t.1 s) (pm s t.1)) ||
    V.all fun v => let x := pm v t.1
      !(G.all fun s => eqPiP pp (pm s x) (pm x s)) || inModPi pp x C

@[expose] def tvOK (e pp z : Nat) (P : List (Nat × Nat)) (E D : List Nat) : Bool :=
  P.all fun t => let cw := fun w => pm (pm (pm w t.1) w) t.2
    !(E.all (fun w => eqPiP pp (cw w) e || eqPiP pp (cw w) z) && E.any (fun w => eqPiP pp (cw w) z)) ||
      D.all fun d => !eqPiP pp (pm (pm t.1 d) t.2) d

@[expose] def transOK (pp b : Nat) (S : List (Nat × Nat)) (X : List Nat) : Bool :=
  (X.zip S).all fun q => eqPiP pp (pm (pm q.2.1 b) q.2.2) q.1

@[expose] def centUOK (z : Wr 6) (C : List (Wr 6)) : Bool :=
  C.all fun c => !(decide (c.perm = 1) && decide (∑ i, c.vec i = 0)) || eqPi c 1 || eqPi c z

@[expose] def dlOK (z : Wr 6) (C D : List (Wr 6)) : Bool :=
  C.all fun c => !(decide (c.perm = 1) && !eqPi c 1 && !eqPi c z) || D.any (eqPi c)

@[expose] def twin3OK (z : Wr 6) (C : List (Wr 6)) : Bool :=
  C.all fun x => !eqPi (x * x) z || C.all fun y =>
    !(eqPi (y * y) 1 && eqPi (y * x * y⁻¹) (x * z)) || decide (y.perm = 1) || decide ((y * x).perm = 1)

@[expose] def twin2OK (L1 L2 : List (Wr 6)) : Bool :=
  Nat.beq L1.length 8 && Nat.beq L2.length 8 &&
    (List.range 8).all fun i =>
      decide ((L1.getD (2 * (i / 2)) 1 * L2.getD i 1).perm = 1) &&
        (List.range i).all fun j =>
          !eqPi (L1.getD (2 * (i / 2)) 1 * L2.getD i 1) (L1.getD (2 * (j / 2)) 1 * L2.getD j 1)

end CFSG.KC.AE6TwinK

end
