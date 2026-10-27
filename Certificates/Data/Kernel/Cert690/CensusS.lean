module

public import Certificates.Data.Kernel.Cert690.Base

public section

namespace CFSG.KC.C690S

open CFSG.KC.C690 CFSG.KC.Enum

@[expose] noncomputable def actS (m v : Nat) : Nat := mulF m (Nat.land v (nat_lit 63))

@[expose] noncomputable def fS (t k : Nat) : Nat :=
  fld(t, Nat.mul (nat_lit 36) k, nat_lit 68719476735)

@[expose] noncomputable def nthS {α : Type} (d : α) (l : List α) : Nat → α :=
  List.rec (motive := fun _ => Nat → α) (fun _ => d)
    (fun x _ ih n => Nat.rec (motive := fun _ => α) x (fun k _ => ih k) n) l

@[expose] noncomputable def memS (x : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => bIf(Nat.beq x y, true, ih)) l

@[expose] noncomputable def allS {α : Type} (f : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => bAnd(f x, ih)) l

@[expose] noncomputable def lenS {α : Type} (l : List α) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def zipS {α β : Type} (f : α → β → Bool) (l₁ : List α) (l₂ : List β) :
    Bool :=
  List.rec (motive := fun _ => List β → Bool)
    (fun l => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) l)
    (fun x _ ih l => List.rec (motive := fun _ => Bool) false (fun y l' _ => bAnd(f x y, ih l')) l)
    l₁ l₂

@[expose] noncomputable def letS (gens : List Nat) (ng r q : Nat) : Nat :=
  nIf(Nat.blt q ng, nthS (nat_lit 0) gens q, r)

@[expose] noncomputable def wvS (L : Nat → Nat) (w : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun a => a)
    (fun q _ ih a => strictN (mulF a (L q)) ih) w

@[expose] noncomputable def wiS (L : Nat → Nat) (w : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun a => a)
    (fun q _ ih a => strictN (mulF (L q) a) ih) w

@[expose] noncomputable def lettersS (n : Nat) (w : List Nat) : Bool :=
  allS (fun q => Nat.blt q n) w

@[expose] noncomputable def pow128 (x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x (fun _ ih => strictN ih fun y => mulF y y) (nat_lit 7)

@[expose] noncomputable def norS (lg lc : List Nat) (y yi : Nat) : Bool :=
  allS (fun x => memS (mulF (mulF y x) yi) lc) lg

@[expose] noncomputable def notOneS (p : Nat) : Bool := bIf(Nat.beq p oneF, false, true)

@[expose] noncomputable def badK (b : Nat) (lg lc : List Nat) (x xi a : Nat) : Bool :=
  (fun nor => bIf(bIf(Nat.beq a b, bIf(nor, false, true), nor), true,
    bAnd(allS (fun y => Nat.beq (mulF x y) (mulF y x)) lg, strictB (pow128 x) notOneS)))
    (norS lg lc x xi)

@[expose] noncomputable def badS (b : Nat) (lg lc : List Nat) (x xi : Nat) : Bool :=
  strictB (actS x b) (badK b lg lc x xi)

@[expose] noncomputable def cparS (nw : Nat) (cpar : List (Nat × Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun pq _ ih i => bAnd(bAnd(Nat.ble pq.1 i, Nat.blt pq.2 nw), ih (Nat.succ i))) cpar

@[expose] noncomputable def cBuild (wv : List Nat) (cpar : List (Nat × Nat)) : Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ c => c)
    (fun pq _ ih i c => strictN (Nat.lor c (Nat.shiftLeft
        (mulF (fS c pq.1) (nthS (nat_lit 0) wv pq.2)) (Nat.mul (nat_lit 36) i)))
      (ih (Nat.succ i))) cpar

@[expose] noncomputable def coverU (spk cpk u pz : Nat) (ρs : List Nat) : Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ s => s)
    (fun ρ _ ih k s => strictN (Nat.lor s
        (nIf(Nat.beq (fS spk ρ) (mulF u (fS cpk k)), Nat.shiftLeft (nat_lit 1) ρ, pz)))
      (ih (Nat.succ k))) ρs

@[expose] noncomputable def coverT (spk cpk pz : Nat) (T : List (Nat × Nat)) :
    List (List Nat) → Nat → Nat :=
  List.rec (motive := fun _ => List (List Nat) → Nat → Nat)
    (fun R s => List.rec (motive := fun _ => Nat) s (fun _ _ _ => Nat.lor s pz) R)
    (fun t _ ih R s => List.rec (motive := fun _ => Nat) (Nat.lor s pz)
      (fun ρs R' _ => strictN (coverU spk cpk (fS spk t.1) pz ρs (nat_lit 0) s) (ih R')) R) T

@[expose] noncomputable def coverS (nS spk : Nat) (gens : List Nat) (wg : List (List Nat))
    (cpar : List (Nat × Nat)) (T : List (Nat × Nat)) (ranks : List (List Nat)) : Bool :=
  (fun ng => bAnd(allS (lettersS ng) wg,
    bAnd(cparS (lenS wg) cpar (nat_lit 0),
    bAnd(allS (fun t => bAnd(bAnd(Nat.blt t.1 nS, Nat.blt t.2 nS),
        Nat.beq (mulF (fS spk t.1) (fS spk t.2)) oneF)) T,
    (fun wv => strictB (cBuild wv cpar (nat_lit 1) oneF) fun cpk =>
      (fun pz => Nat.beq (coverT spk cpk pz T ranks (nat_lit 0)) (Nat.sub pz (nat_lit 1)))
        (Nat.shiftLeft (nat_lit 1) nS))
      (List.map (fun w => wvS (nthS (nat_lit 0) gens) w oneF) wg)))))
  (lenS gens)

@[expose] noncomputable def orbS (sing reps gens qs : List Nat) (ng ns : Nat)
    (orb : List (Nat × Nat × Nat)) : Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) (fun i _ => Nat.beq i ns)
    (fun e _ ih i seen => bAnd(memS e.1 sing, bAnd(Nat.beq (fld(seen, e.1, nat_lit 1)) (nat_lit 0),
      bAnd(bIf(Nat.beq e.2.2 (nat_lit 0), memS e.1 reps,
          bAnd(bAnd(Nat.blt e.2.1 i, Nat.ble e.2.2 ng),
            Nat.beq (actS (nthS (nat_lit 0) gens (Nat.sub e.2.2 (nat_lit 1)))
              (nthS (nat_lit 0) qs e.2.1)) e.1)),
        ih (Nat.succ i) (Nat.lor seen (Nat.shiftLeft (nat_lit 1) e.1)))))) orb

@[expose] noncomputable def closeW (L : Nat → Nat) (na n ni : Nat) (ws : List (List Nat))
    (tg : List Nat) : Bool :=
  zipS (fun w x => bAnd(lettersS na w, Nat.beq (wvS L w oneF) (mulF (mulF n x) ni))) ws tg

@[expose] noncomputable def closK (lg lc : List Nat) (L : Nat → Nat) (na : Nat)
    (ws : List (List Nat)) (tg : List Nat) (n ni p : Nat) : Bool :=
  bAnd(Nat.beq p oneF, bAnd(norS lg lc n ni, closeW L na n ni ws tg))

@[expose] noncomputable def recS (b nS spk nF g ci : Nat) (lg lc fc : List Nat)
    (fg : List (List Nat)) (gens ginv : List Nat) (r ri : Nat) (h : List Nat)
    (ws : List (List Nat)) : Bool :=
  (fun ng tag => bIf(Nat.beq tag (nat_lit 0),
    (fun w => bAnd(lettersS (Nat.succ ng) w,
      strictB (wvS (letS gens ng r) w oneF) fun x =>
      strictB (wiS (letS ginv ng ri) w oneF) fun xi => badS b lg lc x xi))
      (nthS [] ws (nat_lit 0)),
    bIf(Nat.beq tag (nat_lit 1),
      (fun k ρ ρ' => bAnd(bAnd(Nat.blt g k, Nat.blt k nF),
        bAnd(Nat.beq (nthS (nat_lit 0) fc k) ci, bAnd(bAnd(Nat.blt ρ nS, Nat.blt ρ' nS),
        strictB (fS spk ρ) fun n => strictB (fS spk ρ') fun ni =>
        strictB (mulF n ni) (closK lg lc (letS gens ng r) (Nat.succ ng) ws (nthS [] fg k) n ni)))))
        (nthS (nat_lit 0) h (nat_lit 1)) (nthS (nat_lit 0) h (nat_lit 2))
        (nthS (nat_lit 0) h (nat_lit 3)),
      bAnd(Nat.beq tag (nat_lit 2), Nat.beq r oneF))))
  (lenS gens) (nthS (nat_lit 9) h (nat_lit 0))

@[expose] noncomputable def recsT (b nS spk nF g ci : Nat) (lg lc fc : List Nat)
    (fg : List (List Nat)) (gens ginv : List Nat) (t ti : Nat) (T : List (Nat × Nat))
    (rs : List (List Nat × List (List Nat))) : Bool :=
  zipS (fun u e => strictB (mulF t (fS spk u.1)) fun r => strictB (mulF (fS spk u.2) ti) fun ri =>
    recS b nS spk nF g ci lg lc fc fg gens ginv r ri e.1 e.2) T rs

@[expose] noncomputable def spanS (B : List Nat) : List Nat → List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun W => W)
    (fun v _ ih W => ih (List.append W (List.map (fun w => Nat.xor w v) W))) B

@[expose] noncomputable def bothS (gens tg : List Nat) (wa wb : List (List Nat)) : Bool :=
  (fun ng nt =>
    bAnd(zipS (fun w x => bAnd(lettersS ng w, Nat.beq (wvS (nthS (nat_lit 0) gens) w oneF) x)) wa tg,
      zipS (fun w x => bAnd(lettersS nt w, Nat.beq (wvS (nthS (nat_lit 0) tg) w oneF) x)) wb gens))
  (lenS gens) (lenS tg)

@[expose] noncomputable def clsS (pglOK : Bool) (og omg kpg pglc gens : List Nat) (h : List Nat)
    (wa wb : List (List Nat)) : Bool :=
  (fun tag => bIf(Nat.beq tag (nat_lit 1),
    (fun v B => (fun W => bAnd(bAnd(Nat.blt (nat_lit 0) v, Nat.blt v (nat_lit 64)),
        bAnd(Nat.ble (lenS B) (nat_lit 5), bAnd(allS (fun x => Nat.blt x (nat_lit 64)) B,
        bAnd(memS v W, allS (fun x => allS (fun y => memS (actS x y) W) B) gens)))))
      (spanS B [nat_lit 0]))
      (nthS (nat_lit 0) h (nat_lit 1)) (List.tail (List.tail h)),
    bIf(Nat.beq tag (nat_lit 2), bothS gens omg wa wb,
    bIf(Nat.beq tag (nat_lit 3), bothS gens og wa wb,
      bAnd(pglOK, bAnd(Nat.beq tag (nat_lit 4),
        (fun c ci => bAnd(memS c pglc, bAnd(Nat.beq (mulF c ci) oneF,
          bothS gens (List.map (fun x => mulF (mulF c x) ci) kpg) wa wb)))
        (nthS (nat_lit 0) h (nat_lit 1)) (nthS (nat_lit 0) h (nat_lit 2))))))))
  (nthS (nat_lit 0) h (nat_lit 0))

structure SBase where
  pglOK : Bool
  b : Nat
  nS : Nat
  spk : Nat
  nF : Nat
  sing : List Nat
  tpT : List Nat
  tpI : List Nat
  og : List Nat
  omg : List Nat
  kpg : List Nat
  pglc : List Nat
  LG : List (List Nat)
  LC : List (List Nat)
  fc : List Nat
  fg : List (List Nat)

@[expose] noncomputable def checkF (B : SBase) (g : Nat) (ginv : List Nat) (wg : List (List Nat))
    (cpar : List (Nat × Nat)) (T : List (Nat × Nat)) (orb : List (Nat × Nat × Nat))
    (reps : List Nat) (ranks : List (List Nat))
    (recs : List (List (List Nat × List (List Nat))))
    (cls : List Nat × List (List Nat) × List (List Nat)) : Bool :=
  (fun ci gens => (fun lg lc =>
    bAnd(Nat.blt g B.nF,
    bAnd(zipS (fun x y => Nat.beq (mulF x y) oneF) gens ginv,
    bAnd(coverS B.nS B.spk gens wg cpar T ranks,
    bAnd(allS (fun p => memS p B.sing) reps,
    bAnd(orbS B.sing reps gens (List.map (fun e => e.1) orb) (lenS gens) (lenS B.sing) orb
        (nat_lit 0) (nat_lit 0),
    bAnd(zipS (fun p rs => recsT B.b B.nS B.spk B.nF g ci lg lc B.fc B.fg gens ginv
        (nthS (nat_lit 0) B.tpT p) (nthS (nat_lit 0) B.tpI p) T rs) reps recs,
      clsS B.pglOK B.og B.omg B.kpg B.pglc gens cls.1 cls.2.1 cls.2.2)))))))
    (nthS [] B.LG ci) (nthS [] B.LC ci))
  (nthS (nat_lit 0) B.fc g) (nthS [] B.fg g)

@[expose] noncomputable def checkAt (B : SBase) (lo : Nat) (ginv : List (List Nat))
    (wg : List (List (List Nat))) (cpar : List (List (Nat × Nat))) (T : List (List (Nat × Nat)))
    (orb : List (List (Nat × Nat × Nat))) (reps : List (List Nat)) (ranks : List (List (List Nat)))
    (recs : List (List (List (List Nat × List (List Nat)))))
    (cls : List (List Nat × List (List Nat) × List (List Nat))) (i : Nat) : Bool :=
  checkF B (Nat.add lo i) (nthS [] ginv i) (nthS [] wg i) (nthS [] cpar i) (nthS [] T i)
    (nthS [] orb i) (nthS [] reps i) (nthS [] ranks i) (nthS [] recs i)
    (nthS ([], [], []) cls i)

end CFSG.KC.C690S

end
