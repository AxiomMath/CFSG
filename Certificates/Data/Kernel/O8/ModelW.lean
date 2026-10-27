module

public import Certificates.Data.Kernel.O8.Model

public section

namespace CFSG.KC.O8

open CFSG.KLie.CT CFSG.KC.Loop CFSG.KS CFSG.KS.Raw
open CFSG.KC.Enum (pidn pcomp permOK pg)

@[expose] noncomputable def perAt (n w L i : Nat) : Nat := fget L i (Nat.mul n w)

@[expose] noncomputable def oMaskK (n w : Nat) (PSI : Nat → Nat) : Nat :=
  orN n fun z => nIf(allN (nat_lit 63) fun y => notB (Nat.beq (pg w (mask w) (PSI (Nat.succ y)) z) z),
    pw2 z, nat_lit 0)

@[expose] noncomputable def imgMask (n w O G : Nat) : Nat :=
  orN n fun z => Nat.shiftLeft (bitN O (pg w (mask w) G z)) z

@[expose] noncomputable def imgTab (n w O TI m : Nat) : Nat :=
  orN m fun i => Nat.shiftLeft (imgMask n w O (perAt n w TI i)) (Nat.mul n i)

@[expose] noncomputable def oSetOK (n w : Nat) (PSI : Nat → Nat) (cL : ChainK) (PBP pnb nO TL TI m : Nat) :
    Bool :=
  Nat.beq (nat_lit 1) (strictN (oMaskK n w PSI) fun O =>
    nIf(andB (allN pnb fun t => bit O (pg w (mask w) PBP t))
      (andB (allN n fun z => orB (notB (bit O z))
          (anyN (nat_lit 64) fun y => Nat.beq (pg w (mask w) (PSI y) (nat_lit 0)) z))
        (andB (Nat.beq m nO)
          (andB (allN m fun i => andB (permOK n w (mask w) (Nat.mul n w) (perAt n w TL i) (perAt n w TI i))
              (siftCh n w cL (perAt n w TL i)))
            (Nat.beq (nat_lit 1) (strictN (imgTab n w O TI m) fun MT =>
              nIf(allN m fun i => allN i fun j =>
                notB (Nat.beq (fget MT i n) (fget MT j n)), nat_lit 1, nat_lit 0)))))),
      nat_lit 1, nat_lit 0))

@[expose] noncomputable def stabK (n w s M : Nat) : Bool :=
  allN n fun z => orB (notB (bit M z)) (bit M (pg w (mask w) s z))

@[expose] noncomputable def r3OK (n w : Nat) (PSI US : Nat → Nat) (kU TL TI m : Nat) : Bool :=
  andB (Nat.beq (perAt n w TL (nat_lit 0)) (pidn n w))
    (Nat.beq (nat_lit 1) (strictN (imgTab n w (oMaskK n w PSI) TI m) fun MT =>
      nIf(allN m fun i => orB (notB (allN kU fun s => stabK n w (US s) (fget MT i n))) (Nat.beq i (nat_lit 0)),
        nat_lit 1, nat_lit 0)))

@[expose] noncomputable def elemGo (n w : Nat) (LR TR : Nat → Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun t ih r acc => strictN (LR t) fun R => (fun c =>
        ih (Nat.div r c) (pc n w (TR (Nat.add (roff n (Nat.mul n w) R) (Nat.mod r c))) acc))
      (rcnt R))

@[expose] noncomputable def uElemK (n w : Nat) (LR TR : Nat → Nat) (nb i : Nat) : Nat :=
  elemGo n w LR TR nb i (pidn n w)

@[expose] noncomputable def elemInvGo (n w : Nat) (LR TRI : Nat → Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun t ih r acc => strictN (LR t) fun R => (fun c =>
        ih (Nat.div r c) (pc n w acc (TRI (Nat.add (roff n (Nat.mul n w) R) (Nat.mod r c)))))
      (rcnt R))

@[expose] noncomputable def uElemInvK (n w : Nat) (LR TRI : Nat → Nat) (nb i : Nat) : Nat :=
  elemInvGo n w LR TRI nb i (pidn n w)

@[expose] noncomputable def uIdxK (n w : Nat) (LR TRI : Nat → Nat) (BP nb g : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ acc => acc)
    (fun _ ih l g acc => strictN (LR l) fun R =>
      strictN (rpos w (mask w) (Nat.mul n w) R (pg w (mask w) g (pg w (mask w) BP l))) fun k =>
        nIf(Nat.blt k (rcnt R),
          ih (Nat.succ l) (pc n w (TRI (Nat.add (roff n (Nat.mul n w) R) k)) g)
            (Nat.add (Nat.mul acc (rcnt R)) k),
          nat_lit 4096))
    nb (nat_lit 0) g (nat_lit 0)

structure ChainT where
  LR : Nat → Nat
  TR : Nat → Nat
  TRI : Nat → Nat
  BP : Nat
  nb : Nat

@[expose] noncomputable def chOf (c : ChainT) : ChainK := ⟨c.LR, c.TRI, c.BP, c.nb⟩

@[expose] noncomputable def elemT (n w : Nat) (c : ChainT) (i : Nat) : Nat := uElemK n w c.LR c.TR c.nb i
@[expose] noncomputable def elemInvT (n w : Nat) (c : ChainT) (i : Nat) : Nat :=
  uElemInvK n w c.LR c.TRI c.nb i
@[expose] noncomputable def idxT (n w : Nat) (c : ChainT) (g : Nat) : Nat := uIdxK n w c.LR c.TRI c.BP c.nb g

@[expose] noncomputable def isInvolK (n w x : Nat) : Bool :=
  andB (notB (Nat.beq x (pidn n w))) (Nat.beq (pc n w x x) (pidn n w))

@[expose] noncomputable def blk (b k : Nat) : Nat := Nat.add (Nat.mul (nat_lit 256) b) k

@[expose] noncomputable def s5ElemOK (n w : Nat) (cU : ChainT) (b : Nat) : Bool :=
  allN (nat_lit 256) fun k => (fun i => Nat.beq (nat_lit 1) (strictN (elemT n w cU i) fun S =>
      nIf(andB (permOK n w (mask w) (Nat.mul n w) S (elemInvT n w cU i))
        (andB (siftCh n w (chOf cU) S) (Nat.beq (idxT n w cU S) i)), nat_lit 1, nat_lit 0)))
    (blk b k)

@[expose] noncomputable def clsAt (CLS i : Nat) : Nat := fget CLS i (nat_lit 19)

@[expose] noncomputable def s5ClsOK (n w : Nat) (cU : ChainT) (CLS REPS NC b : Nat) : Bool :=
  allN (nat_lit 256) fun k => (fun i => (fun e => Nat.beq (nat_lit 1) (strictN (elemT n w cU i) fun S =>
      nIf(Bool.rec (motive := fun _ => Bool)
          ((fun c j => andB (Nat.blt c NC) (andB (isInvolK n w S)
            (Nat.beq S (pc n w (pc n w (elemT n w cU j) (elemT n w cU (fget REPS c (nat_lit 12))))
              (elemInvT n w cU j))))) (Nat.sub (Nat.land e (nat_lit 127)) (nat_lit 1)) (Nat.shiftRight e (nat_lit 7)))
          (notB (isInvolK n w S)) (Nat.beq e (nat_lit 0)), nat_lit 1, nat_lit 0)))
      (clsAt CLS i))
    (blk b k)

@[expose] noncomputable def s5RepOK (CLS REPS NC : Nat) : Bool :=
  allN NC fun c => Nat.beq (Nat.land (clsAt CLS (fget REPS c (nat_lit 12))) (nat_lit 127)) (Nat.succ c)

@[expose] noncomputable def adjAt (ADJ NC c c' : Nat) : Bool := bit ADJ (Nat.add (Nat.mul NC c) c')

@[expose] noncomputable def s5AdjNegOK (n w : Nat) (cU : ChainT) (CLS REPS NC ADJ b : Nat) : Bool :=
  allN (nat_lit 8) fun k => (fun c => orB (notB (Nat.blt c NC))
      (Nat.beq (nat_lit 1) (strictN (elemT n w cU (fget REPS c (nat_lit 12))) fun R =>
        nIf(allN NC fun c' => orB (adjAt ADJ NC c c')
            (anyN (nat_lit 4096) fun y => andB (Nat.beq (Nat.land (clsAt CLS y) (nat_lit 127)) (Nat.succ c'))
              ((fun Y => notB (Nat.beq (pc n w R Y) (pc n w Y R))) (elemT n w cU y))),
          nat_lit 1, nat_lit 0))))
    (Nat.add (Nat.mul (nat_lit 8) b) k)

@[expose] noncomputable def s5SizeOK (CLS NC SZ : Nat) : Bool :=
  allN NC fun c => Nat.beq (fget SZ c (nat_lit 12))
    (sumBelow (nat_lit 4096) (nat_lit 64) fun y =>
      nIf(Nat.beq (Nat.land (clsAt CLS y) (nat_lit 127)) (Nat.succ c), nat_lit 1, nat_lit 0))

@[expose] noncomputable def selK (d e : Nat) : Bool :=
  andB (notB (Nat.beq e (nat_lit 0))) (bit d (Nat.sub (Nat.land e (nat_lit 127)) (nat_lit 1)))

@[expose] noncomputable def wordC (n w : Nat) (S SI : Nat → Nat) (wd : List Int) : Nat :=
  wordK n w (mask w) (pidn n w) S SI wd

@[expose] noncomputable def finalK (n w : Nat) (cU : ChainT) (cL : ChainK) (CLS a l li d : Nat) : Bool :=
  andB (siftCh n w cL l) (andB (permOK n w (mask w) (Nat.mul n w) l li)
    (andB (notB (Nat.beq (pc n w (pc n w l a) li) a))
      (allN (nat_lit 4096) fun i => orB (notB (selK d (clsAt CLS i)))
        ((fun y => (fun kk => andB (Nat.blt kk (nat_lit 4096))
            (andB (Nat.beq y (elemT n w cU kk)) (selK d (clsAt CLS kk))))
          (idxT n w cU y)) (pc n w (pc n w l (elemT n w cU i)) li)))))

@[expose] noncomputable def enumK (NC ADJ SZ : Nat) (leaf : Nat → Bool) : Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool)
    (fun d s => orB (notB (Nat.beq s (nat_lit 63))) (leaf d))
    (fun r ih d s => (fun t => andB (ih d s)
        (orB (notB (andB (adjAt ADJ NC t t) (allN t fun c' => orB (notB (bit d c')) (adjAt ADJ NC c' t))))
          (ih (Nat.lor d (pw2 t)) (Nat.add s (fget SZ t (nat_lit 12))))))
      (Nat.sub NC (Nat.succ r)))

@[expose] noncomputable def s5EnumOK (n w : Nat) (cU : ChainT) (cL : ChainK) (S SI : Nat → Nat)
    (CLS NC ADJ SZ a : Nat) (cands : List (List Int)) : Bool :=
  enumK NC ADJ SZ (fun d => List.rec (motive := fun _ => Bool) false
      (fun wd _ ih => orB (finalK n w cU cL CLS a (wordC n w S SI wd)
        (wordC n w S SI (List.reverse (List.map (fun x => Int.neg x) wd))) d) ih) cands)
    NC (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def q3OK (n w : Nat) (UA US : Nat → Nat) (kU : Nat) (cP : ChainK)
    (FL FI m FA FB : Nat) (G8 G8I : Nat) (UT : Nat → Nat) (cU : ChainK) (PSI2 TG : Nat → Nat) : Bool :=
  (fun R2 R2I => andB (allN (nat_lit 6) fun k => Nat.beq (pg w (mask w) (UA k) (nat_lit 0)) (nat_lit 0))
    (andB (Nat.beq m (nat_lit 315))
      (andB (Nat.beq (perAt n w FL (nat_lit 0)) (pidn n w))
        (andB (allN m fun j => andB (permOK n w (mask w) (Nat.mul n w) (perAt n w FL j) (perAt n w FI j))
            (siftCh n w cP (perAt n w FL j)))
          (andB (Nat.beq (nat_lit 1) (strictN (imgTab n w FA FI m) fun MA => strictN (imgTab n w FB FI m) fun MB =>
              nIf(andB (allN m fun j => allN j fun j' => orB (notB (Nat.beq (fget MA j n) (fget MA j' n)))
                    (notB (Nat.beq (fget MB j n) (fget MB j' n))))
                  (allN m fun j => orB (notB (allN kU fun s =>
                      andB (stabK n w (US s) (fget MA j n)) (stabK n w (US s) (fget MB j n)))) (Nat.beq j (nat_lit 0))),
                nat_lit 1, nat_lit 0)))
            (andB (allN kU fun s => andB (stabK n w (US s) FA) (stabK n w (US s) FB))
              (andB (permOK (nat_lit 360) (nat_lit 9) (mask (nat_lit 9)) (nat_lit 3240) R2 R2I)
                (andB (allN (nat_lit 6) fun k => andB
                    (Nat.beq (Nat.land (UT k) (maskN (Nat.mul n w))) (UA k))
                    (siftCh n w cU (Nat.land (pc (nat_lit 360) (nat_lit 9) (pc (nat_lit 360) (nat_lit 9) R2 (UT k)) R2I)
                      (maskN (Nat.mul n w)))))
                  (allN (nat_lit 6) fun j => Nat.beq
                    (Nat.land (pc (nat_lit 360) (nat_lit 9) (pc (nat_lit 360) (nat_lit 9) R2 (PSI2 j)) R2I)
                      (maskN (Nat.mul n w))) (TG j))))))))))
    (pc (nat_lit 360) (nat_lit 9) G8 G8) (pc (nat_lit 360) (nat_lit 9) G8I G8I)

end CFSG.KC.O8

end
