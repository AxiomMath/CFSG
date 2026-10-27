module

public import CFSG.Sporadic.Presentation.Fi22ExactData
public import Certificates.Data.Kernel.HOrb
public import CFSG.Certificates.Kernel.Common.HOrb
public import Mathlib

public section

namespace CFSG.KC.Fi22F.Walks

open CFSG.KC CFSG.KC.LceS CFSG.KC.HOrb CFSG.Sporadic.Presentation.Fi22Exact

@[expose] noncomputable def digits (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun c _ acc => Nat.add c (Nat.mul (nat_lit 256) acc)) l

@[expose] noncomputable def entL (l : List Nat) : Nat :=
  Nat.add (Nat.mul (nat_lit 4) l.length) (Nat.mul (nat_lit 4096) (digits l))

@[expose] noncomputable def entW (l : List Nat) : Nat :=
  Nat.add (entL l) (Nat.shiftLeft (nat_lit 1) (Nat.add (nat_lit 12) (Nat.mul (nat_lit 8) l.length)))

@[expose] noncomputable def code (p : Fin 6 × Bool) : Nat :=
  Nat.add (Nat.mul (nat_lit 2) p.1.val) (Bool.rec (motive := fun _ => Nat) (nat_lit 1) (nat_lit 0) p.2)

@[expose] noncomputable def pos (l : List Nat) : List Nat := l.map fun g => Nat.mul (nat_lit 2) g

@[expose] noncomputable def relsBind (RT : Nat → Nat) (ws : List (List (Fin 6 × Bool))) (k₀ : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun w _ ih k => andB (Nat.beq (RT k) (entL (w.map code))) (ih (Nat.succ k))) ws k₀

@[expose] noncomputable def posBind (ST : Nat → Nat) (ws : List (List Nat)) (k₀ : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun w _ ih k => andB (Nat.beq (ST k) (entL (pos w))) (ih (Nat.succ k))) ws k₀

@[expose] def sWords : List (List Nat) :=
  [0] :: ((qrels.filter fun q => q.1.val == 0 && q.2.2.1.val == 0).map fun q =>
    q.2.1.map (·.val) ++ (q.2.2.2.map (·.val)).reverse)

@[expose] noncomputable def lt6 (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun g _ ih => andB (Nat.blt g (nat_lit 6)) ih) l

@[expose] noncomputable def wordsLt (ws : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun w _ ih => andB (andB (lt6 w) (Nat.blt w.length (nat_lit 1024))) ih) ws

@[expose] noncomputable def relsLt (ws : List (List (Fin 6 × Bool))) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun w _ ih => andB (Nat.blt w.length (nat_lit 1024)) ih) ws

@[expose] def Ew (c : List Nat) : List Nat := c.reverse ++ 0 :: c

@[expose] def pW (cs : List (List Nat)) (i : Nat) (w : List Nat) : List Nat :=
  cs.getD i [] ++ w.flatMap fun g => Ew (cs.getD g [])

@[expose] def xrL (i : Nat) (w : List Nat) (j m : Nat) : List Nat :=
  (List.replicate m (w.reverse.map (fun g => 2 * g + 1) ++ [2 * i] ++ w.map (fun g => 2 * g) ++ [2 * j])).flatten

@[expose] def walk2 (cs : List (List Nat)) (i : Nat) (w : List Nat) (j : Nat) : List Nat :=
  pW cs i w ++ Ew (cs.getD j []) ++ (pW cs i w).reverse

@[expose] def walk3 (cs : List (List Nat)) (i : Nat) (w : List Nat) (j : Nat) : List Nat :=
  pW cs i w ++ Ew (cs.getD j []) ++ (cs.getD j [] ++ Ew (pW cs i w)).reverse

@[expose] noncomputable def csOK (cs : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun c _ ih => andB (lt6 c) ih) cs

@[expose] noncomputable def wk (blk : Nat → Nat) (nf : Nat) (l : List Nat) (R : Nat) : Bool :=
  andB (Nat.blt l.length (nat_lit 1024)) (walkTo blk nf (entW (pos l)) (nat_lit 0) R (nat_lit 0))

@[expose] noncomputable def pairOK (blk : Nat → Nat) (nf : Nat) (cs : List (List Nat)) (XR : Nat)
    (pr : Nat × List Nat × Nat × Nat × Nat) : Bool :=
  andB (Nat.beq XR (entL (xrL pr.1 pr.2.1 pr.2.2.1 pr.2.2.2.1)))
    (andB (Nat.blt (xrL pr.1 pr.2.1 pr.2.2.1 pr.2.2.2.1).length (nat_lit 1024))
    (andB (Nat.blt pr.1 (nat_lit 6)) (andB (Nat.blt pr.2.2.1 (nat_lit 6))
    (andB (lt6 pr.2.1)
    (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (andB (Nat.beq pr.2.2.2.1 (nat_lit 3)) (wk blk nf (walk3 cs pr.1 pr.2.1 pr.2.2.1) pr.2.2.2.2))
        (wk blk nf (walk2 cs pr.1 pr.2.1 pr.2.2.1) pr.2.2.2.2)
        (Nat.beq pr.2.2.2.1 (nat_lit 2)))
      (andB (Nat.beq pr.1 pr.2.2.1) (Nat.beq pr.2.1.length (nat_lit 0)))
      (Nat.beq pr.2.2.2.1 (nat_lit 1)))))))

@[expose] noncomputable def pairsOK (blk : Nat → Nat) (nf : Nat) (cs : List (List Nat)) (XRs : Nat → Nat)
    (prs : List (Nat × List Nat × Nat × Nat × Nat)) (k₀ : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun pr _ ih k => andB (pairOK blk nf cs (XRs k) pr) (ih (Nat.succ k))) prs k₀

@[expose] noncomputable def hgOne (blk : Nat → Nat) (nf : Nat) (cs : List (List Nat))
    (h : List Nat × Nat × List Nat × Nat) : Bool :=
  andB (Nat.blt h.2.1 (nat_lit 6)) (andB (andB (lt6 h.2.2.1) (lt6 h.1))
    (wk blk nf (pW cs h.2.1 h.2.2.1 ++ h.1.reverse) h.2.2.2))

@[expose] noncomputable def hgOK (blk : Nat → Nat) (nf : Nat) (cs : List (List Nat))
    (hs : List (List Nat × Nat × List Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun h _ ih => andB (hgOne blk nf cs h) ih) hs

end CFSG.KC.Fi22F.Walks

end
