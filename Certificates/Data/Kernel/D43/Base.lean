module

public import Certificates.Data.Kernel.D43.Twin
public import CFSG.Milestones.ASVolI.F48.D43.Data
public import Mathlib

public section

namespace CFSG.KC.D43

open CFSG.KC.Enum CFSG.ASVolI

@[expose] noncomputable def dPt (F P : Nat → Nat) (d p : Nat) : Nat :=
  nIf(Nat.blt d (nat_lit 8), tabAt F d p,
    nIf(Nat.blt d (nat_lit 16),
      strictN (tabAt F (Nat.sub d (nat_lit 8)) p) (tabAt F (Nat.sub d (nat_lit 8))),
      nIf(Nat.beq d (nat_lit 16), tabAt P (nat_lit 0) p,
        strictN (tabAt P (nat_lit 0) p) (tabAt P (nat_lit 0)))))

@[expose] noncomputable def wPt (F P : Nat → Nat) (w : List Nat) (p : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun d _ ih p => strictN (ih p) (dPt F P d)) w p

@[expose] noncomputable def cntD (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun d _ ih => Nat.add (nIf(Nat.blt d (nat_lit 16), nat_lit 0,
      nIf(Nat.beq d (nat_lit 16), nat_lit 1, nat_lit 2))) ih) w

@[expose] def baseL : List Nat := [0, 26571, 6, 479, 15916, 186, 1, 3]

@[expose] noncomputable def fixL (F P : Nat → Nat) (w bs : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun b _ ih => bAnd(Nat.beq (wPt F P w b) b, ih)) bs

@[expose] noncomputable def wOK (F P : Nat → Nat) (w : List Nat) : Bool :=
  bAnd(Nat.beq (Nat.mod (cntD w) (nat_lit 3)) (nat_lit 0), fixL F P w baseL)

@[expose] def invW {m : Nat} (w : List (Fin m × Bool)) : List (Fin m × Bool) :=
  (w.map fun l => (l.1, !l.2)).reverse

@[expose] def digG (l : Fin 8 × Bool) : Nat := cond l.2 l.1.val (l.1.val + 8)

@[expose] def flatG (w : List (Fin 8 × Bool)) : List Nat := w.map digG

@[expose] def flatL (LW : List (List (Fin 8 × Bool))) (l : Fin 18 × Bool) : List Nat :=
  if l.1.val = 2 then [cond l.2 16 17]
  else flatG (cond l.2 (LW.getD (if l.1.val < 2 then l.1.val else l.1.val - 1) [])
    (invW (LW.getD (if l.1.val < 2 then l.1.val else l.1.val - 1) [])))

@[expose] def flatX (LW : List (List (Fin 8 × Bool))) (r : List (Fin 18 × Bool)) : List Nat :=
  (r.map (flatL LW)).flatten

@[expose] def xy6W : List (Fin 18 × Bool) := (List.replicate 6 [(0, true), (1, true)]).flatten

@[expose] def relWs : List (List (Fin 18 × Bool)) :=
  burnsideF48d_R13 ++ burnsideF48d_R23 ++ [xy6W]

@[expose] noncomputable def relChunk (F P : Nat → Nat) (c : Nat) : Bool :=
  allBlk (Nat.mul (nat_lit 5) c)
    (fun i => wOK F P (flatX burnsideF48d_LW (relWs.getD i []))) (nat_lit 5)

end CFSG.KC.D43

end
