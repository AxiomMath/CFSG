module

public import Certificates.Data.Kernel.WrTwin
public import Certificates.Data.E64Aut

public noncomputable section

namespace CFSG.KC.E64AutK

open CFSG.KC.WrTwin CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
  Certificates.AE117 Certificates.E64Aut

@[expose] def pm (x y : Nat) : Nat := pmul 14 x y

@[expose] def lvl (σ : Equiv.Perm (Fin 7)) : Nat × Nat := (enc (ofPerm σ), enc (ofPerm σ)⁻¹)

@[expose] def pairMul (a b : Nat × Nat) : Nat × Nat := (pm a.1 b.1, pm b.2 a.2)

@[expose] def prods (e : Nat) : List (List (Nat × Nat)) → List (Nat × Nat)
  | [] => [(e, e)]
  | E :: L => E.flatMap fun a => (prods e L).map (pairMul a)

@[expose] def vecL (l : List (ZMod 2)) : Fin 7 → ZMod 2 := fun i => l.getD i.val 0

@[expose] def allL : Nat → List (List (ZMod 2))
  | 0 => [[]]
  | n + 1 => (allL n).flatMap fun l => [0 :: l, 1 :: l]

@[expose] def vecs : List (Fin 7 → ZMod 2) := (allL 7).map vecL

@[expose] def V64 : List Nat :=
  ((vecs.filter fun v => decide (∑ i, v i = 0))).map fun v => enc (ofVec v)

@[expose] def pw (e : Nat) (T : List Nat) : List Nat → Nat
  | [] => e
  | k :: w => w.foldl (fun acc k => pm acc (T.getD k e)) (T.getD k e)

@[expose] def tab (L : List (Wr 7)) : List Nat := L.flatMap fun x => [enc x, enc x⁻¹]

@[expose] def inPiP (e pp p : Nat) : Bool := Nat.beq p e || Nat.beq p pp

@[expose] def inModPi (pp y : Nat) (B : List Nat) : Bool :=
  B.any (fun b => Nat.beq y b) || B.any (fun b => Nat.beq (pm y pp) b)

@[expose] def relsK : List (List Nat) := [rels.getD 0 [], rels.getD 1 [], rels.getD 10 []]

@[expose] def samePerm (p q : Nat) : Bool :=
  (List.range 7).all fun i => Nat.beq (nib p (2 * i) / 2) (nib q (2 * i) / 2)

@[expose] def quads : List (Fin 7 × Fin 7 × Fin 7 × Fin 7) :=
  [(2, 4, 5, 6), (0, 3, 5, 6), (0, 1, 4, 6), (0, 1, 2, 5), (1, 2, 3, 6), (0, 2, 3, 4), (1, 3, 4, 5)]

@[expose] def memQ (q : Fin 7 × Fin 7 × Fin 7 × Fin 7) (b : Bool) : List (Wr 7) :=
  memLC q.1 q.2.1 q.2.2.1 q.2.2.2 b

@[expose] def twinQ (q : Fin 7 × Fin 7 × Fin 7 × Fin 7) : List (Wr 7) := memQ q true ++ memQ q false

@[expose] def membersQ : List (Wr 7) := quads.flatMap twinQ

@[expose] def quadSteps : List ((Fin 7 × Fin 7 × Fin 7 × Fin 7) × (Fin 7 × Fin 7 × Fin 7 × Fin 7)) :=
  quads.zip (quads.tail ++ quads.take 1)

@[expose] def rho : Equiv.Perm (Fin 7) := CFSG.ClassicalInvolution.Q3.E64Data.cycPerm [[0, 1, 2, 3, 4, 5, 6]]

@[expose] def centOK (e pp : Nat) (P : List (Nat × Nat)) (V S : List Nat) : Bool :=
  P.all fun t => !(S.all fun s => samePerm (pm t.1 s) (pm s t.1)) ||
    V.all fun v => !(S.all fun s => inModPi pp (pm (pm v t.1) s) [pm s (pm v t.1)]) ||
      inPiP e pp (pm v t.1)

@[expose] def solOK (e pp : Nat) (R : List (List Nat)) (P : List (Nat × Nat)) (V TW cg : List Nat) :
    Bool :=
  P.all fun t => !(R.all fun r => samePerm (pw e (TW ++ [t.1, t.2]) r) e) ||
    V.all fun v => !(R.all fun r => inPiP e pp (pw e (TW ++ [pm v t.1, pm t.2 v]) r)) ||
      inModPi pp (pm v t.1) cg

@[expose] def memOK (e pp : Nat) (T ys : List Nat) : Bool :=
  ys.all fun y => inModPi pp y (words0.map (pw e T))

@[expose] def conjIn (pp s si : Nat) (A B : List Nat) : Bool :=
  A.all fun a => inModPi pp (pm (pm s a) si) B

end CFSG.KC.E64AutK

end
