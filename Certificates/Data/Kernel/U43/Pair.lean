module

public import Certificates.Data.Kernel.U43.Class
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434U43CoverCheck

public section

namespace CFSG.KD.U43

open CFSG.KC.Loop CFSG.RankThree.PartTwo.Sec4.Item434RemU43

@[expose] noncomputable def wf (w i : Nat) : Nat := Nat.land (Nat.shiftRight w (Nat.mul 10 i)) 1023

@[expose] noncomputable def pw (c c2 k : Nat) : Nat := nIf(Nat.beq k 0, ONEF, nIf(Nat.beq k 1, c, c2))

@[expose] noncomputable def o3F (x x2 : Nat) : Bool := !(Nat.beq x ONEF) && Nat.beq (MF x x2) ONEF

@[expose] noncomputable def elsF (Z Z2 A A2 B B2 e : Nat) : Nat :=
  letN (Nat.div e 3) fun m => letN (MF (pw Z Z2 (Nat.div m 3)) (pw A A2 (Nat.mod m 3))) fun u =>
    letN (Nat.mod e 3) fun k => nIf(Nat.beq k 0, u, nIf(Nat.beq k 1, MF u B, MF u B2))

@[expose] noncomputable def e9F (A A2 B B2 e : Nat) : Nat :=
  MF (pw A A2 (Nat.div e 3)) (pw B B2 (Nat.mod e 3))

@[expose] noncomputable def inRtF (X : Nat → Nat) (ca cb y r : Nat) : Bool :=
  !(Nat.beq y ONEF) && Nat.blt r 729 && memF r uRt && Nat.beq (X r) (MF (MF ca y) cb)

@[expose] noncomputable def goodF (X KND CA CB E : Nat → Nat) (w : Nat) : Bool :=
  letB (wf w 1) fun x => Nat.blt 0 x && Nat.blt x 27 &&
  allBelow x 1 (fun i => letB (wf w (Nat.add 6 i)) fun q => Nat.blt q 729 &&
    Nat.beq (X q) (E (Nat.succ i)) &&
    bIf(Nat.beq (Nat.succ i) x, Nat.beq (KND q) 2, !(Nat.beq (KND q) 2))) &&
  letB (wf w (Nat.add 5 x)) fun q => letB (wf w 2) fun u => letB (wf w 3) fun v =>
  Nat.blt u 27 && Nat.blt v 27 && letB (E u) fun U => letB (E v) fun V =>
    inRtF X (CA q) (CB q) U (wf w 4) && inRtF X (CA q) (CB q) V (wf w 5) &&
    !(Nat.beq V U) && !(Nat.beq V (MF U U))

@[expose] noncomputable def badF (X E : Nat → Nat) (w : Nat) : Bool :=
  letB (wf w 1) fun k => letB (wf w 2) fun ea => letB (wf w 3) fun eb =>
  Nat.blt k 12 && Nat.blt ea 27 && Nat.blt eb 27 &&
  letB ((badTriple k).getD 1 0) fun pa => letB ((badTriple k).getD 2 0) fun pb =>
    Nat.blt pa 729 && Nat.blt pb 729 && Nat.beq (E ea) (X pa) && Nat.beq (E eb) (X pb)

@[expose] noncomputable def ppF (X SQ KND CA CB : Nat → Nat) (Z Z2 ia ib w : Nat) : Bool :=
  letB (X ia) fun a => letB (X ib) fun b => letB (wf w 0) fun c =>
  bIf(Nat.beq c 1, Nat.beq a Z || Nat.beq a Z2,
  bIf(Nat.beq c 2, letB (wf w 1) fun m =>
      Nat.blt m 9 && Nat.beq b (MF (pw Z Z2 (Nat.div m 3)) (pw a (SQ ia) (Nat.mod m 3))),
  bIf(Nat.beq c 3, goodF X KND CA CB (elsF Z Z2 a (SQ ia) b (SQ ib)) w,
  bIf(Nat.beq c 4, badF X (elsF Z Z2 a (SQ ia) b (SQ ib)) w, false))))

@[expose] noncomputable def cvF (X SQ CA CB : Nat → Nat) (ia ib w : Nat) : Bool :=
  letB (wf w 0) fun c =>
  bIf(Nat.beq c 1, Nat.beq (X ib) (SQ ia),
  bIf(Nat.beq c 2, letB (wf w 1) fun t => letB (wf w 2) fun q =>
      letB (e9F (X ia) (SQ ia) (X ib) (SQ ib) (Nat.succ t)) fun e =>
      Nat.blt t 8 && Nat.blt q 729 && Nat.beq (X q) e && inRtF X (CA q) (CB q) e (wf w 3),
  bIf(Nat.beq c 3, letB (wf w 1) fun n => Nat.blt n 13 &&
      allBelow 3 1 fun i => letB (wf w (Nat.add 2 i)) fun t => letB (wf w (Nat.add 5 i)) fun q =>
        letB ((yTriple n).getD i 0) fun y =>
        letB (e9F (X ia) (SQ ia) (X ib) (SQ ib) (Nat.succ t)) fun e =>
        Nat.blt t 8 && Nat.blt q 729 && Nat.blt y 729 && Nat.beq (X q) e &&
          !(Nat.beq e ONEF) && commF (X y) (X q), false)))

@[expose] noncomputable def pairsF (X SQ KND CA CB OL WP WC : Nat → Nat) (Z Z2 lo m : Nat) :
    Bool :=
  allBelow m 1 fun j => letB (Nat.add lo j) fun j₁ => letB (OL j₁) fun ia => letB (X ia) fun a =>
    allBelow 296 5 fun j₂ => letB (OL j₂) fun ib =>
      bIf(Nat.blt ia ib, bIf(commF a (X ib),
        letB (Nat.add (Nat.mul 296 j₁) j₂) fun k =>
          ppF X SQ KND CA CB Z Z2 ia ib (WP k) && cvF X SQ CA CB ia ib (WC k), true), true)

@[expose] noncomputable def sqF (X SQ : Nat → Nat) : Bool :=
  allBelow 729 12 fun t => Nat.beq (SQ t) (MF (X t) (X t))

@[expose] noncomputable def olF (X SQ OL OLI : Nat → Nat) : Bool :=
  allBelow 729 12 fun t =>
    bIf(o3F (X t) (SQ t), Nat.blt (OLI t) 296 && Nat.beq (OL (OLI t)) t, true)

@[expose] noncomputable def listF (K : Nat → Nat) (l : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun k _ ih p => bAnd(Nat.beq (K p) k, ih (Nat.succ p))) l

@[expose] noncomputable def convF (A CA CB : Nat → Nat) : Bool :=
  allBelow 729 12 fun q => Nat.beq (CA q) (wordF A (convRWord q)) &&
    Nat.beq (CB q) (wordF A (invWord (convRWord q)))

@[expose] noncomputable def yElF (X SQ : Nat → Nat) (p₀ p₁ p₂ e : Nat) : Nat :=
  MF (MF (pw (X p₀) (SQ p₀) (Nat.div e 9)) (pw (X p₁) (SQ p₁) (Nat.mod (Nat.div e 3) 3)))
    (pw (X p₂) (SQ p₂) (Nat.mod e 3))

@[expose] noncomputable def distF (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a t ih => bAnd(!(memF a t), ih)) l

@[expose] noncomputable def yF (X SQ A YR : Nat → Nat) (n : Nat) : Bool :=
  letB ((yTriple n).getD 0 0) fun p₀ => letB ((yTriple n).getD 1 0) fun p₁ =>
  letB ((yTriple n).getD 2 0) fun p₂ =>
  allBelow 3 1 (fun i => allBelow 3 1 fun j =>
    commF (X ((yTriple n).getD i 0)) (X ((yTriple n).getD j 0))) &&
  allBelow 3 1 (fun i => Nat.beq (MF (X ((yTriple n).getD i 0)) (SQ ((yTriple n).getD i 0))) ONEF) &&
  distF ((List.range 27).map (yElF X SQ p₀ p₁ p₂)) &&
  allBelow 3 1 fun i => letB (YR (Nat.add (Nat.mul 3 n) i)) fun r =>
    Nat.blt r 729 && memF r uRt && Nat.beq (X r) (wconjF A (yWord n) (X ((yTriple n).getD i 0)))

@[expose] noncomputable def liftF (X : Nat → Nat) (i : Nat) : Nat := X (uLiftBasis.getD i 0)

@[expose] noncomputable def liftRhsF (X : Nat → Nat) (j i : Nat) : Nat :=
  MF (powF (liftF X 0) (liftMat j 0 i)) (MF (powF (liftF X 1) (liftMat j 1 i))
    (MF (powF (liftF X 2) (liftMat j 2 i)) (MF (powF (liftF X 3) (liftMat j 3 i)) ONEF)))

@[expose] noncomputable def liftK (X A : Nat → Nat) : Bool :=
  allBelow 2 1 fun j => allBelow 4 1 fun i =>
    Nat.beq (wconjF A (uLiftG.getD j []) (liftF X i)) (liftRhsF X j i)

end CFSG.KD.U43

end
