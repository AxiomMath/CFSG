module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KD.Sp4Ov

open CFSG.KC.Loop

@[expose] noncomputable def col (c i : Nat) : Nat := fld(c, Nat.shiftLeft i (nat_lit 2), nat_lit 15)

@[expose] noncomputable def mv (a v : Nat) : Nat :=
  Nat.xor
    (Nat.xor (Nat.mul fld(a, nat_lit 0, nat_lit 15) fld(v, nat_lit 0, nat_lit 1))
      (Nat.mul fld(a, nat_lit 4, nat_lit 15) fld(v, nat_lit 1, nat_lit 1)))
    (Nat.xor (Nat.mul fld(a, nat_lit 8, nat_lit 15) fld(v, nat_lit 2, nat_lit 1))
      (Nat.mul fld(a, nat_lit 12, nat_lit 15) fld(v, nat_lit 3, nat_lit 1)))

@[expose] noncomputable def mulP (a b : Nat) : Nat :=
  Nat.lor
    (Nat.lor (mv a fld(b, nat_lit 0, nat_lit 15))
      (Nat.shiftLeft (mv a fld(b, nat_lit 4, nat_lit 15)) (nat_lit 4)))
    (Nat.lor (Nat.shiftLeft (mv a fld(b, nat_lit 8, nat_lit 15)) (nat_lit 8))
      (Nat.shiftLeft (mv a fld(b, nat_lit 12, nat_lit 15)) (nat_lit 12)))

@[expose] noncomputable def oneP : Nat := nat_lit 33825

@[expose] noncomputable def memP (m c : Nat) : Bool :=
  Nat.blt (nat_lit 0) (Nat.land m (Nat.shiftLeft (nat_lit 1) c))

@[expose] noncomputable def subP (m m' : Nat) : Bool := Nat.beq (Nat.land m m') m

@[expose] noncomputable def bJK (u w : Nat) : Nat :=
  Nat.land (Nat.xor
    (Nat.xor (Nat.land u (Nat.shiftRight w (nat_lit 3))) (Nat.land (Nat.shiftRight u (nat_lit 3)) w))
    (Nat.xor (Nat.land (Nat.shiftRight u (nat_lit 1)) (Nat.shiftRight w (nat_lit 2)))
      (Nat.land (Nat.shiftRight u (nat_lit 2)) (Nat.shiftRight w (nat_lit 1))))) (nat_lit 1)

@[expose] noncomputable def isSympK (c : Nat) : Bool :=
  bAnd(Nat.beq (bJK (col c 0) (col c 1)) 0, bAnd(Nat.beq (bJK (col c 0) (col c 2)) 0,
    bAnd(Nat.beq (bJK (col c 0) (col c 3)) 1, bAnd(Nat.beq (bJK (col c 1) (col c 2)) 1,
      bAnd(Nat.beq (bJK (col c 1) (col c 3)) 0, Nat.beq (bJK (col c 2) (col c 3)) 0)))))

@[expose] noncomputable def allP : Nat :=
  Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 65536)) (nat_lit 1)

@[expose] noncomputable def plane (k : Nat) : Nat :=
  Nat.mul (Nat.div allP (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.shiftLeft (nat_lit 2) k)) (nat_lit 1)))
    (Nat.shiftLeft (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.shiftLeft (nat_lit 1) k)) (nat_lit 1))
      (Nat.shiftLeft (nat_lit 1) k))

@[expose] noncomputable def bJPl (i j : Nat) : Nat :=
  (fun a b => Nat.xor
    (Nat.xor (Nat.land (plane a) (plane (Nat.add b 3))) (Nat.land (plane (Nat.add a 3)) (plane b)))
    (Nat.xor (Nat.land (plane (Nat.add a 1)) (plane (Nat.add b 2)))
      (Nat.land (plane (Nat.add a 2)) (plane (Nat.add b 1)))))
  (Nat.shiftLeft i (nat_lit 2)) (Nat.shiftLeft j (nat_lit 2))

@[expose] noncomputable def sympMaskK : Nat :=
  Nat.land (Nat.land (Nat.xor (bJPl 0 1) allP) (Nat.xor (bJPl 0 2) allP))
    (Nat.land (Nat.land (bJPl 0 3) (bJPl 1 2))
      (Nat.land (Nat.xor (bJPl 1 3) allP) (Nat.xor (bJPl 2 3) allP)))

@[expose] noncomputable def elemsOK (spM : Nat) : Bool := Nat.beq sympMaskK spM

abbrev RepR := Nat × Nat × Nat × List (List Nat) × List Nat

abbrev NodeR := Nat × List Nat × List Nat × List RepR

@[expose] def NodeR.mask (s : NodeR) : Nat := s.1

@[expose] def NodeR.gens (s : NodeR) : List Nat := s.2.1

@[expose] def NodeR.tree (s : NodeR) : List Nat := s.2.2.1

@[expose] def NodeR.reps (s : NodeR) : List RepR := s.2.2.2

@[expose] def RepR.r (p : RepR) : Nat := p.1

@[expose] def RepR.ri (p : RepR) : Nat := p.2.1

@[expose] def RepR.t (p : RepR) : Nat := p.2.2.1

@[expose] def RepR.words (p : RepR) : List (List Nat) := p.2.2.2.1

@[expose] def RepR.cover (p : RepR) : List Nat := p.2.2.2.2

@[expose] noncomputable def memL (l : List Nat) (g : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun h _ ih => bIf(Nat.beq h g, true, ih)) l

@[expose] noncomputable def allMem (m : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun h _ ih => bAnd(memP m h, ih)) l

@[expose] noncomputable def treeStep (gens : List Nat) (m e : Nat) : Nat :=
  (fun y z g => nIf(bAnd(memP m z, bAnd(bIf(memP m y, false, true),
      bAnd(memL gens g, Nat.beq (mulP z g) y))), Nat.lor m (Nat.shiftLeft (nat_lit 1) y), nat_lit 0))
    fld(e, nat_lit 0, nat_lit 65535) fld(e, nat_lit 16, nat_lit 65535) (Nat.shiftRight e (nat_lit 32))

@[expose] noncomputable def treeK (gens : List Nat) (tr : List Nat) (m : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun m => m)
    (fun e _ ih m => strictN (treeStep gens m e) ih) tr m

@[expose] noncomputable def evalW (m r : Nat) (w : List Nat) (acc : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun l _ ih acc => nIf(bIf(memP m l, true, Nat.beq l r), ih (mulP acc l), nat_lit 1048576)) w acc

@[expose] noncomputable def wordOK (m r g : Nat) (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun hd tl _ => bAnd(Nat.beq hd g, Nat.beq (evalW m r tl oneP) g)) w

@[expose] noncomputable def wordsOK (m r : Nat) (gens : List Nat) (ws : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => List (List Nat) → Bool)
    (fun ws => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) ws)
    (fun g _ ih ws => List.rec (motive := fun _ => Bool) false
      (fun w ws' _ => bAnd(wordOK m r g w, ih ws')) ws) gens ws

@[expose] def nodeZ : NodeR := (0, [], [], [])

@[expose] noncomputable def getN (L : List NodeR) : Nat → NodeR :=
  List.rec (motive := fun _ => Nat → NodeR) (fun _ => nodeZ)
    (fun h _ ih i => Nat.rec (motive := fun _ => NodeR) h (fun j _ => ih j) i) L

@[expose] noncomputable def repOK (L : List NodeR) (m : Nat) (p : RepR) : Bool :=
  bAnd(bIf(memP m p.r, false, true), bAnd(Nat.blt p.ri (nat_lit 65536),
    bAnd(Nat.beq (mulP p.ri p.r) oneP,
      (fun t => bAnd(subP m t.mask, bAnd(memP t.mask p.r, wordsOK m p.r t.gens p.words)))
        (getN L p.t))))

@[expose] noncomputable def covK (m ri : Nat) (cov : List Nat) (acc : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun e _ ih acc => strictN ((fun x a => nIf(bAnd(memP m a, memP m (mulP (mulP ri a) x)),
        Nat.lor acc (Nat.shiftLeft (nat_lit 1) x), acc))
      fld(e, nat_lit 0, nat_lit 65535) (Nat.shiftRight e (nat_lit 16))) ih) cov acc

@[expose] noncomputable def covAll (m : Nat) (reps : List RepR) (acc : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun p _ ih acc => strictN (covK m p.ri p.cover acc) ih) reps acc

@[expose] noncomputable def nodeK (spM : Nat) (L : List NodeR) (s : NodeR) : Bool :=
  bAnd(memP s.mask oneP, bAnd(subP s.mask spM, bAnd(allMem s.mask s.gens,
    bAnd(Nat.beq (treeK s.gens s.tree (Nat.shiftLeft (nat_lit 1) oneP)) s.mask,
      bAnd(List.rec (motive := fun _ => Bool) true (fun p _ ih => bAnd(repOK L s.mask p, ih)) s.reps,
        Nat.beq (Nat.lor s.mask (covAll s.mask s.reps (nat_lit 0))) spM)))))

@[expose] noncomputable def ovK (spM : Nat) (L : List NodeR) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun s _ ih => bAnd(nodeK spM L s, ih)) L

end CFSG.KD.Sp4Ov

end
