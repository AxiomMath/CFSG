module

public import Certificates.Data.Kernel.Misc.PermClos

public section

namespace CFSG.KC.SpinOrb

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.Clos

abbrev Q4 : Type := Nat × Nat × Nat × Nat

@[expose] noncomputable def lane (w x i : Nat) : Nat :=
  Nat.land (Nat.shiftRight x (Nat.mul w i)) (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1))

@[expose] noncomputable def ofLanes (w N : Nat) (f : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.add acc (Nat.shiftLeft (f i) (Nat.mul w i))) N

@[expose] noncomputable def smallK (w b N x : Nat) : Bool :=
  andB (Nat.beq (Nat.shiftRight x (Nat.mul w N)) (nat_lit 0))
    (allN N fun i => Nat.blt (lane w x i) (Nat.shiftLeft (nat_lit 1) b))

@[expose] noncomputable def gP (g r : Nat) : Nat := Nat.shiftRight (lane (nat_lit 8) g r) (nat_lit 1)

@[expose] noncomputable def gS (g r : Nat) : Nat := Nat.land (lane (nat_lit 8) g r) (nat_lit 1)

@[expose] noncomputable def relAt (gi gj : Nat) (same : Bool) (r : Nat) : Bool :=
  letB (gP gi r) fun pi => letB (gP gj r) fun pj =>
    Bool.rec (motive := fun _ => Bool)
      (andB (Nat.beq (gP gj pi) (gP gi pj))
        (notB (Nat.beq (Nat.mod (Nat.add (gS gi r) (gS gj pi)) (nat_lit 2))
          (Nat.mod (Nat.add (gS gj r) (gS gi pj)) (nat_lit 2)))))
      (andB (Nat.beq (gP gi pi) r) (Nat.beq (gS gi r) (gS gi pi))) same

@[expose] noncomputable def gamRelK (n N : Nat) (G : List Nat) : Bool :=
  andB (andB (Nat.beq G.length n)
      (allL G fun g => andB (Nat.beq (Nat.shiftRight g (Nat.mul (nat_lit 8) N)) (nat_lit 0))
        (allN N fun r => Nat.blt (gP g r) N)))
    (allN n fun i => allN n fun j => allN N (relAt (G.getD i 0) (G.getD j 0) (Nat.beq i j)))

@[expose] noncomputable def prefixK (m : Nat) (G G' : List Nat) : Bool :=
  allN m fun k => Nat.beq (G'.getD k 0) (G.getD k 0)

@[expose] noncomputable def kronIK (m N : Nat) (G G' : List Nat) : Bool :=
  allN m fun k => Nat.beq (G'.getD k 0)
    (ofLanes (nat_lit 8) (Nat.add N N) fun s =>
      kronE (lane (nat_lit 8) (G.getD k 0) (Nat.shiftRight s (nat_lit 1))) s)
where
  kronE (e s : Nat) : Nat :=
    Nat.add (Nat.mul (nat_lit 4) (Nat.shiftRight e (nat_lit 1)))
      (Nat.add (Nat.mul (nat_lit 2) (Nat.land s (nat_lit 1))) (Nat.land e (nat_lit 1)))

@[expose] noncomputable def permP (W N g X Y : Nat) : Nat :=
  ofLanes W N fun r =>
    lane W (Bool.rec (motive := fun _ => Nat) X Y (Nat.beq (gS g r) (nat_lit 1))) (gP g r)

@[expose] noncomputable def gamA (W N g P M : Nat) (k : Nat → Nat → Bool) : Bool :=
  letB (permP W N g P M) fun P' => letB (permP W N g M P) fun M' => k P' M'

@[expose] noncomputable def ddA (W N : Nat) (G : List Nat) (q : Q4) (P M : Nat)
    (k : Nat → Nat → Bool) : Bool :=
  gamA W N (G.getD q.2.2.1 0) P M fun Pc Mc => gamA W N (G.getD q.2.2.2 0) P M fun Pd Md =>
    letB (Nat.add Pc Md) fun Pu => letB (Nat.add Mc Pd) fun Mu =>
      gamA W N (G.getD q.1 0) Pu Mu fun Pa Ma => gamA W N (G.getD q.2.1 0) Pu Mu fun Pb Mb =>
        k (Nat.add Pa Mb) (Nat.add Ma Pb)

@[expose] noncomputable def wordA (W N : Nat) (G : List Nat) (w : List Q4) : Nat → Nat →
    (Nat → Nat → Bool) → Bool :=
  List.rec (motive := fun _ => Nat → Nat → (Nat → Nat → Bool) → Bool) (fun P M k => k P M)
    (fun q _ ih P M k => ih P M fun P' M' => ddA W N G q P' M' k) w

@[expose] noncomputable def invW (w : List Q4) : List Q4 :=
  List.rec (motive := fun _ => List Q4) [] (fun q _ ih => ih ++ [(q.2.2.1, q.2.2.2, q.1, q.2.1)]) w

@[expose] noncomputable def seqW (p : List Q4 × List Q4) : List Q4 :=
  p.1 ++ (p.2 ++ (invW p.1 ++ invW p.2))

@[expose] noncomputable def wordsOK (n : Nat) (p : List Q4 × List Q4) : Bool :=
  andB (allLQ (p.1 ++ p.2) fun q =>
      andB (Nat.blt q.1 n) (andB (Nat.blt q.2.1 n) (andB (Nat.blt q.2.2.1 n)
        (andB (Nat.blt q.2.2.2 n) (andB (notB (Nat.beq q.1 q.2.1))
          (notB (Nat.beq q.2.2.1 q.2.2.2)))))))
    (andB (Nat.ble (nat_lit 2) (seqW p).length) (Nat.ble (seqW p).length (nat_lit 24)))
where
  allLQ (l : List Q4) (f : Q4 → Bool) : Bool :=
    List.rec (motive := fun _ => Bool) true (fun x _ ih => andB (f x) ih) l

@[expose] noncomputable def allPairs (l : List (List Q4 × List Q4)) (f : List Q4 × List Q4 → Bool) :
    Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => andB (f x) ih) l

@[expose] noncomputable def idM (N : Nat) : Nat :=
  ofLanes (Nat.mul (nat_lit 64) N) N fun r => Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 64) r)

@[expose] noncomputable def colsOK (N P M e : Nat) (R : List (Nat × Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun c _ ih j => andB
      (andB (andB (smallK (nat_lit 64) (nat_lit 16) N c.1) (smallK (nat_lit 64) (nat_lit 16) N c.2))
        (allN N fun r =>
          Nat.beq (Nat.add (lane (nat_lit 64) (lane (Nat.mul (nat_lit 64) N) P r) j)
              (Nat.shiftLeft (lane (nat_lit 64) c.2 r) e))
            (Nat.add (lane (nat_lit 64) (lane (Nat.mul (nat_lit 64) N) M r) j)
              (Nat.shiftLeft (lane (nat_lit 64) c.1 r) e))))
      (ih (Nat.succ j))) R

@[expose] noncomputable def matOK (N : Nat) (G : List Nat) (p : List Q4 × List Q4)
    (R : List (Nat × Nat)) : Bool :=
  andB (Nat.beq R.length N)
    (wordA (Nat.mul (nat_lit 64) N) N G (seqW p) (idM N) (nat_lit 0) fun P M =>
      letB (Nat.sub (seqW p).length (nat_lit 2)) fun e => colsOK N P M e R (nat_lit 0))

@[expose] noncomputable def blk (N T k : Nat) : Nat := lane (Nat.mul (nat_lit 64) N) T k

@[expose] noncomputable def mvA (R : List (Nat × Nat)) (b : Nat) (k : Nat → Nat → Bool) : Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Bool) (fun _ A B => k A B)
    (fun c _ ih x A B => letB (Nat.land x (nat_lit 18446744073709551615)) fun v =>
      letB (Nat.add A (Nat.add (Nat.mul v c.1) (Nat.mul (nat_lit 128) c.2))) fun A' =>
        letB (Nat.add B (Nat.add (Nat.mul v c.2) (Nat.mul (nat_lit 128) c.1))) fun B' =>
          ih (Nat.shiftRight x (nat_lit 64)) A' B') R b (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def ones (N : Nat) : Nat := ofLanes (nat_lit 64) N fun _ => nat_lit 1

@[expose] noncomputable def mvOK (N : Nat) (R : List (Nat × Nat)) (b c : Nat) : Bool :=
  andB (smallK (nat_lit 64) (nat_lit 8) N c)
    (mvA R b fun A B => Nat.beq (Nat.add A (Nat.mul (nat_lit 512) (ones N)))
      (Nat.add B (Nat.mul (nat_lit 4) c)))

@[expose] noncomputable def sigOK (N S : Nat) (R : List (List (Nat × Nat))) (T Sg k : Nat)
    (l : Nat) : Bool :=
  letB (lane (nat_lit 8) (lane (Nat.mul (nat_lit 8) S) Sg l) k) fun m =>
    andB (Nat.blt m S) (mvOK N (R.getD l []) (blk N T k) (blk N T m))

@[expose] noncomputable def invOK (S nF Sg k l : Nat) : Bool :=
  letB (lane (Nat.mul (nat_lit 8) S) Sg l) fun f => letB (lane (Nat.mul (nat_lit 8) S) Sg
    (Nat.add nF l)) fun b =>
      andB (andB (Nat.blt (lane (nat_lit 8) b k) S)
        (Nat.beq (lane (nat_lit 8) f (lane (nat_lit 8) b k)) k))
        (Nat.beq (lane (nat_lit 8) b (lane (nat_lit 8) f k)) k)

@[expose] noncomputable def orbAt (N S : Nat) (R : List (List (Nat × Nat))) (T Sg k : Nat) : Bool :=
  andB (smallK (nat_lit 64) (nat_lit 8) N (blk N T k))
    (andB (allN R.length (sigOK N S R T Sg k)) (allN R.length (invOK S R.length Sg k)))

@[expose] noncomputable def treeOK (S nL Sg Tr k : Nat) : Bool :=
  letB (lane (nat_lit 16) Tr k) fun r =>
    Bool.rec (motive := fun _ => Bool)
      (letB (Nat.land r (nat_lit 255)) fun p => letB (Nat.shiftRight r (nat_lit 8)) fun l =>
        andB (Nat.blt p k) (andB (Nat.blt l nL)
          (Nat.beq (lane (nat_lit 8) (lane (Nat.mul (nat_lit 8) S) Sg l) p) k)))
      (Nat.beq r (nat_lit 0)) (Nat.beq k (nat_lit 0))

@[expose] noncomputable def lamOK (S Sg Tr L k : Nat) : Bool :=
  letB (lane (Nat.mul (nat_lit 8) S) L k) fun lk =>
    Bool.rec (motive := fun _ => Bool)
      (letB (lane (nat_lit 16) Tr k) fun r =>
        letB (lane (Nat.mul (nat_lit 8) S) L (Nat.land r (nat_lit 255))) fun lp =>
          letB (lane (Nat.mul (nat_lit 8) S) Sg (Nat.shiftRight r (nat_lit 8))) fun s =>
            Nat.beq lk (ofLanes (nat_lit 8) S fun j => lane (nat_lit 8) s (lane (nat_lit 8) lp j)))
      (Nat.beq lk (ofLanes (nat_lit 8) S fun j => j)) (Nat.beq k (nat_lit 0))

@[expose] noncomputable def lamAt (S L i j : Nat) : Nat :=
  lane (nat_lit 8) (lane (Nat.mul (nat_lit 8) S) L i) j

@[expose] noncomputable def orbitK (N S : Nat) (R : List (List (Nat × Nat))) (T Sg Tr L SG k : Nat) :
    Bool :=
  andB (andB (orbAt N S R T Sg k) (treeOK S (Nat.add R.length R.length) Sg Tr k))
    (andB (lamOK S Sg Tr L k) (sortAt S (blk N T) (lane (nat_lit 8) SG) k))

@[expose] noncomputable def psiW (n : Nat) (w : List Q4) : Nat :=
  List.rec (motive := fun _ => Nat) (one n)
    (fun q _ ih => mul n (mul n (swap n q.1 q.2.1) (swap n q.2.2.1 q.2.2.2)) ih) w

@[expose] noncomputable def psiC (n : Nat) (p : List Q4 × List Q4) : Nat :=
  mul n (mul n (mul n (psiW n p.1) (psiW n p.2)) (inv n (psiW n p.1))) (inv n (psiW n p.2))

@[expose] noncomputable def gensEq (n : Nat) (ps : List (List Q4 × List Q4)) (gs : List Nat) :
    Bool :=
  andB (Nat.beq ps.length gs.length)
    (List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
      (fun p _ ih l => andB (Nat.beq (l.headD (nat_lit 0)) (psiC n p)) (ih l.tail)) ps gs)

@[expose] noncomputable def psiAt (n N : Nat) (gs : List Nat) (E PA SG CT k : Nat) : Bool :=
  andB (andB (treeAt (mul n) (one n) (fun j => gs.getD j 0) gs.length (lane (nat_lit 64) E)
      (lane (nat_lit 32) PA) k) (sortAt N (lane (nat_lit 64) E) (lane (nat_lit 8) SG) k))
    (closedAt (mul n) (fun j => gs.getD j 0) gs.length N (lane (nat_lit 64) E)
      (lane (nat_lit 8) CT) k)

@[expose] noncomputable def abelOK (S nF Tr L : Nat) (A : List Nat) : Bool :=
  andB (andB (Nat.beq (A.headD (nat_lit 1)) (nat_lit 0))
      (allN nF fun g => Nat.beq (lane (nat_lit 16) Tr (Nat.succ g)) (Nat.mul (nat_lit 256) g)))
    (andB (strictK A)
      (allL A fun a => andB (Nat.blt a S) (andB (Nat.beq (lamAt S L a a) (nat_lit 0))
        (andB (allL A fun b => anyL A fun c => Nat.beq (lamAt S L a b) c)
          (allN nF fun g => anyL A fun b =>
            Nat.beq (lamAt S L (Nat.succ g) a) (lamAt S L b (Nat.succ g)))))))
where
  strictK (l : List Nat) : Bool :=
    (List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun x _ ih p => andB (Nat.blt p x) (ih x)) l.tail) (l.headD (nat_lit 0))

@[expose] noncomputable def kleinAt (S L K idx : Nat) : Bool :=
  letB (lane (nat_lit 32) K idx) fun e =>
    letB (Nat.land e (nat_lit 255)) fun p => letB (Nat.land (Nat.shiftRight e (nat_lit 8)) (nat_lit 255)) fun q =>
      andB (andB (Nat.blt p S) (Nat.blt q S))
      (andB (Nat.beq (lamAt S L p p) (nat_lit 0)) (andB (Nat.beq (lamAt S L q q) (nat_lit 0))
        (andB (Nat.beq (lamAt S L p q) (lamAt S L q p))
          (andB (notB (Nat.beq p (nat_lit 0))) (andB (notB (Nat.beq q (nat_lit 0)))
            (andB (notB (Nat.beq p q))
              (andB (Nat.beq (Nat.land (Nat.shiftRight e (nat_lit 16)) (nat_lit 255)) (lamAt S L p q))
                (Bool.rec (motive := fun _ => Bool)
                  (letB (Nat.shiftRight e (nat_lit 24)) fun par =>
                    letB (lane (nat_lit 32) K par) fun f =>
                      letB (Nat.land f (nat_lit 255)) fun p' =>
                        letB (Nat.land (Nat.shiftRight f (nat_lit 8)) (nat_lit 255)) fun q' =>
                          andB (Nat.blt par idx)
                            (andB (andB (Nat.beq (lamAt S L p p') (lamAt S L p' p))
                              (Nat.beq (lamAt S L p q') (lamAt S L q' p)))
                              (andB (Nat.beq (lamAt S L q p') (lamAt S L p' q))
                                (Nat.beq (lamAt S L q q') (lamAt S L q' q)))))
                  true (Nat.beq idx (nat_lit 0))))))))))

@[expose] noncomputable def invAt (S L : Nat) (I : List Nat) (i : Nat) : Bool :=
  Nat.beq (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
      (andB (Nat.beq (lamAt S L i i) (nat_lit 0)) (notB (Nat.beq i (nat_lit 0)))))
    (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (anyL I fun x => Nat.beq x i))

@[expose] noncomputable def inRec (e i : Nat) : Bool :=
  orB (Nat.beq i (nat_lit 0)) (orB (Nat.beq i (Nat.land e (nat_lit 255)))
    (orB (Nat.beq i (Nat.land (Nat.shiftRight e (nat_lit 8)) (nat_lit 255)))
      (Nat.beq i (Nat.land (Nat.shiftRight e (nat_lit 16)) (nat_lit 255)))))

@[expose] noncomputable def pairsAt (S L K nK : Nat) (I : List Nat) (Wt a : Nat) : Bool :=
  letB (I.getD a 0) fun i =>
    (List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun j _ ih b => andB
        (orB (Nat.beq i j) (orB (notB (Nat.beq (lamAt S L i j) (lamAt S L j i)))
          (letB (lane (nat_lit 8) Wt (Nat.add (Nat.mul a I.length) b)) fun w =>
            andB (Nat.blt w nK) (letB (lane (nat_lit 32) K w) fun e => andB (inRec e i) (inRec e j)))))
        (ih (Nat.succ b))) I) (nat_lit 0)

end CFSG.KC.SpinOrb

end
