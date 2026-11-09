module

public import CFSG.LocalAnalysis.ComponentClassification.ExactGenCert
public import Certificates.Data.Kernel.Misc.ArrEnum
public import Certificates.Data.Kernel.Spor.Raw
public import Mathlib

public section

namespace CFSG.KC.ExactGen

open CFSG.ComponentClassification.SolMax.SwapP2.ExactFin
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum
open CFSG.Monster.B.Co2.Native (lettersOK)

variable (n w : ℕ)

@[expose] noncomputable def pkA (a : Array ℕ) : ℕ := (packL w a.toList).1

@[expose] noncomputable def bndA (a : Array ℕ) : Bool :=
  arrBind a n w (pkA w a) && permB n w (pkA w a)

@[expose] noncomputable def pc (p q : ℕ) : ℕ := pcomp n w (mask w) p q

@[expose] noncomputable def pid : ℕ := pidn n w

@[expose] noncomputable def SC (cd : ChainData) (h : ℕ) : ℕ := pkA w cd.S[h]!

@[expose] noncomputable def SIC (cd : ChainData) (h : ℕ) : ℕ := pinvS n w (mask w) (SC w cd h)

@[expose] noncomputable def wK (cd : ChainData) (wd : List ℤ) : ℕ :=
  wordK n w (mask w) (pidn n w) (SC w cd) (SIC n w cd) wd

@[expose] noncomputable def letK (cd : ChainData) (l : ℤ) : ℕ :=
  if 0 < l then SC w cd (l.toNat - 1) else SIC n w cd ((-l).toNat - 1)

@[expose] noncomputable def ppw (p k : ℕ) : ℕ := ppow n w (mask w) (pidn n w) p k

@[expose] noncomputable def hashK (p : ℕ) : ℕ :=
  foldUp n (fun i h => Nat.mod (Nat.add (Nat.mul h 1000003) (pg w (mask w) p i))
    2305843009213693951) 7

@[expose] noncomputable def chainBK (cd : ChainData) : Bool :=
  (List.range cd.S.size).all fun j => bndA n w cd.S[j]!

@[expose] noncomputable def origsK (H amb : ChainData) (ws : List (List ℤ)) : Bool :=
  Nat.beq ws.length H.k && (List.range H.k).all fun i =>
    lettersOK amb.S.size ws[i]! && Nat.beq (SC w H i) (wK n w amb ws[i]!)

@[expose] noncomputable def ctxK (c : Ctx) : Bool :=
  decide (c.chP.k ≤ c.chN.k) && decide (0 < c.chP.base.length) &&
    (List.range c.chP.k).all (fun i => Nat.beq (SC w c.chN i) (SC w c.chP i)) &&
    (List.range (c.chN.k - c.chP.k)).all (fun a => (List.range c.chP.k).all (fun p =>
      lettersOK c.chP.S.size c.normW[a * c.chP.k + p]! &&
      Nat.beq (pc n w (pc n w (SC w c.chN (c.chP.k + a)) (SC w c.chP p)) (SIC n w c.chN (c.chP.k + a)))
        (wK n w c.chP c.normW[a * c.chP.k + p]!))) &&
    decide (c.transW.length = n) &&
    (List.range n).all (fun ω => lettersOK c.chP.S.size c.transW[ω]! &&
      Nat.beq (pg w (mask w) (wK n w c.chP c.transW[ω]!) c.b0) ω) &&
    c.stabLetters.all (fun j => decide (0 < j) && decide (j ≤ c.chP.S.size) &&
      Nat.beq (pg w (mask w) (SC w c.chP (j - 1)) c.b0) c.b0) &&
    (List.range n).all (fun ω => ω == c.b0 ||
      c.stabLetters.any (fun j => !(Nat.beq (pg w (mask w) (SC w c.chP (j - 1)) ω) ω))) &&
    decide (c.b0 < n)

@[expose] noncomputable def coverK (T K : ChainData) (cc : CoverCert) (nrep : ℕ) (repK : ℕ → ℕ)
    (oT : ℕ) : Bool :=
  cc.ws.all (lettersOK T.S.size) &&
    strictInc (cc.ws.map fun wd => hashK n w (wK n w T wd)) &&
    Nat.beq cc.ws.length oT && Nat.beq cc.cj.length cc.ws.length &&
    (List.range cc.ws.length).all fun i =>
      !(Nat.beq (pc n w (wK n w T cc.ws[i]!) (wK n w T cc.ws[i]!)) (pid n w)) ||
      Nat.beq (wK n w T cc.ws[i]!) (pid n w) ||
      (decide (1 ≤ (cc.cj[i]!).1 ∧ (cc.cj[i]!).1 ≤ nrep) && lettersOK K.S.size (cc.cj[i]!).2 &&
        Nat.beq (pc n w (wK n w K (cc.cj[i]!).2) (wK n w K (winv (cc.cj[i]!).2))) (pid n w) &&
        Nat.beq (pc n w (pc n w (wK n w K (cc.cj[i]!).2) (wK n w T cc.ws[i]!))
          (wK n w K (winv (cc.cj[i]!).2))) (repK (cc.cj[i]!).1))

@[expose] noncomputable def parOK (cd : ChainData) (BT : ℕ → ℕ) : ℕ → List (ℕ × ℤ) → Bool
  | _, [] => true
  | m, (p, l) :: rest =>
    Nat.beq (BT (m + 1)) (pc n w (pc n w (letK n w cd l) (BT p)) (letK n w cd (-l))) &&
      parOK cd BT (m + 1) rest

@[expose] noncomputable def ptKeyK (B : List ℕ) (p : ℕ) : ℕ :=
  B.foldl (fun h b => h * n + (if b < n then pg w (mask w) p b else 0)) 0

@[expose] noncomputable def setKeyK (k q : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun j ih => Nat.lor ih (Nat.shiftLeft 1 (pg w (mask w) q j))) k

@[expose] noncomputable def fixBitsK (p : ℕ) : ℕ :=
  foldUp n (fun i h => if Nat.beq (pg w (mask w) p i) i then Nat.lor h (Nat.shiftLeft 1 i) else h) 0

@[expose] noncomputable def fixNumK (p : ℕ) : ℕ :=
  foldUp n (fun i c => if Nat.beq (pg w (mask w) p i) i then c + 1 else c) 0

@[expose] noncomputable def imgSetK (k : ℕ) (L : ℤ → ℕ) (FT : ℕ → ℕ) : ℕ → List (ℕ × ℤ) → Bool
  | _, [] => true
  | m, (p, l) :: rest =>
    Nat.beq (FT (m + 1)) (pcomp k w (mask w) (L l) (FT p)) && imgSetK k L FT (m + 1) rest

@[expose] noncomputable def fixOrbK (cd : ChainData) (seed : ℕ) (par : List (ℕ × ℤ)) (ord : List ℕ)
    (FT : ℕ → ℕ) : Bool :=
  Nat.blt (fixNumK n w seed) 4294967296 &&
    Nat.beq (setKeyK w (fixNumK n w seed) (FT 0)) (fixBitsK n w seed) &&
    imgSetK w (fixNumK n w seed) (letK n w cd) FT 0 par &&
    strictInc (ord.map fun m => setKeyK w (fixNumK n w seed) (FT m))

@[expose] noncomputable def relRowK (k p ra rb : ℕ) : Bool :=
  (List.range k).all fun j => rb.testBit (pg w (mask w) p (pg w (mask w) ra j))

@[expose] noncomputable def relMapK (k : ℕ) (RP : ℕ → ℕ) (p : ℕ) : Bool :=
  (List.range n).all fun a => relRowK w k p (RP a) (setKeyK w k (RP (pg w (mask w) p a)))

@[expose] noncomputable def relBitsK (kr : ℕ) (RP : ℕ → ℕ) (p : ℕ) : ℕ :=
  foldUp n (fun i h => if (setKeyK w kr (RP i)).testBit (pg w (mask w) p i) then
    Nat.lor h (Nat.shiftLeft 1 i) else h) 0

@[expose] noncomputable def relOrbK (cd : ChainData) (seed : ℕ) (R : List ℕ) (kr : ℕ)
    (RP : ℕ → ℕ) (k : ℕ) (par : List (ℕ × ℤ)) (ord : List ℕ) (FT : ℕ → ℕ) : Bool :=
  Nat.blt k 4294967296 &&
    (List.range n).all (fun a => Nat.beq R[a]! (setKeyK w kr (RP a))) &&
    (List.range cd.k).all (fun i => relMapK n w kr RP (SC w cd i) &&
      relMapK n w kr RP (SIC n w cd i)) &&
    Nat.beq (setKeyK w k (FT 0)) (relBitsK n w kr RP seed) &&
    imgSetK w k (letK n w cd) FT 0 par &&
    strictInc (ord.map fun m => setKeyK w k (FT m))

@[expose] noncomputable def relNumK (kr : ℕ) (RP : ℕ → ℕ) (p : ℕ) : ℕ :=
  foldUp n (fun i c => if (setKeyK w kr (RP i)).testBit (pg w (mask w) p i) then c + 1 else c) 0

@[expose] noncomputable def relOrbL (cd : ChainData) (seed : ℕ) (R RL : List ℕ) (kr : ℕ)
    (par : List (ℕ × ℤ)) (ord : List ℕ) (FT : ℕ → ℕ) : Bool :=
  relOrbK n w cd seed R kr (fun a => RL[a]!) (relNumK n w kr (fun a => RL[a]!) seed) par ord FT

@[expose] noncomputable def bfsK (cd : ChainData) (B R RL : List ℕ) (kr seed : ℕ)
    (par : List (ℕ × ℤ)) (ord : List ℕ) (BT : ℕ → ℕ) : Bool :=
  bfsOK cd.S.size par 1 && ord.all (fun m => decide (m < par.length + 1)) &&
    Nat.beq (BT 0) seed && parOK n w cd BT 0 par &&
    (strictInc (ord.map fun m => hashK n w (BT m)) ||
      strictInc (ord.map fun m => ptKeyK n w B (BT m))) ||
  bfsOK cd.S.size par 1 && ord.all (fun m => decide (m < par.length + 1)) &&
    (fixOrbK n w cd seed par ord BT || relOrbL n w cd seed R RL kr par ord BT)

@[expose] noncomputable def abK (chP chC : ChainData) (g : GenCert) : List ℕ :=
  g.Aw.map (wK n w chC) ++ g.Bw.map (wK n w chP)

@[expose] noncomputable def genK (chP chC : ChainData) (g : GenCert) (nu enu : ℕ) : Bool :=
  g.Aw.all (lettersOK chC.S.size) && g.Bw.all (lettersOK chP.S.size) &&
    decide (g.ka.length = g.Aw.length) && decide (g.kb.length = g.Bw.length) &&
    (List.range g.Aw.length).all (fun i =>
      decide (g.ka[i]! % 2 = 1) &&
        Nat.beq (pc n w nu (wK n w chC g.Aw[i]!)) (pc n w (wK n w chC g.Aw[i]!) nu) &&
        Nat.beq (ppw n w (wK n w chC g.Aw[i]!) g.ka[i]!) (pid n w)) &&
    (List.range g.Bw.length).all (fun i =>
      decide (g.kb[i]! % 2 = 1) &&
        Nat.beq (pc n w enu (wK n w chP g.Bw[i]!)) (pc n w (wK n w chP g.Bw[i]!) enu) &&
        Nat.beq (ppw n w (wK n w chP g.Bw[i]!) g.kb[i]!) (pid n w)) &&
    decide (g.pw.length = chP.k) &&
    (List.range chP.k).all (fun i =>
      lettersOK (abK n w chP chC g).length g.pw[i]! &&
      Nat.beq (SC w chP i) (wordK n w (mask w) (pidn n w) (fun h => (abK n w chP chC g)[h]!)
        (fun h => pinvS n w (mask w) (abK n w chP chC g)[h]!) g.pw[i]!))

@[expose] noncomputable def repK (ctx : Ctx) (r : RepCert) (BT : ℕ → ℕ) (oP oC oX oT : ℕ) : Bool :=
  lettersOK ctx.chN.S.size r.nuW &&
  Nat.beq (pc n w (wK n w ctx.chN r.nuW) (wK n w ctx.chN r.nuW)) (pid n w) &&
  origsK n w r.chC ctx.chP r.cgW &&
  (List.range r.chC.k).all (fun i =>
    Nat.beq (pc n w (wK n w ctx.chN r.nuW) (SC w r.chC i)) (pc n w (SC w r.chC i) (wK n w ctx.chN r.nuW))) &&
  bfsK n w ctx.chP ctx.chN.base ctx.rel ctx.relP ctx.relK (wK n w ctx.chN r.nuW) r.par r.ord BT &&
  decide (oP ≤ r.ord.length * oC) &&
  origsK n w r.chX r.chC r.xgW &&
  (List.range r.chC.k).all (fun i => (List.range r.chX.k).all (fun j =>
    lettersOK r.chX.S.size ((r.xnorm[i]!)[j]!) &&
      Nat.beq (pc n w (pc n w (SC w r.chC i) (SC w r.chX j)) (SIC n w r.chC i))
        (wK n w r.chX ((r.xnorm[i]!)[j]!)))) &&
  (List.range r.chC.k).all (fun i => (List.range r.chC.k).all (fun i' =>
    lettersOK r.chX.S.size ((r.xcomm[i]!)[i']!) &&
      Nat.beq (pc n w (pc n w (SC w r.chC i) (SC w r.chC i')) (pc n w (SIC n w r.chC i) (SIC n w r.chC i')))
        (wK n w r.chX ((r.xcomm[i]!)[i']!)))) &&
  origsK n w r.chT r.chX r.tgW && Nat.beq oT (2 ^ r.sylA) && Nat.beq oX (2 ^ r.sylA * r.sylM) &&
  decide (r.sylM % 2 = 1) && r.epsW.all (lettersOK r.chX.S.size) &&
  coverK n w r.chT r.chC r.tel r.epsW.length (fun k => wK n w r.chX (r.epsW[k - 1]!)) oT &&
  decide (r.gens.length = r.epsW.length) &&
  (List.range r.epsW.length).all (fun l =>
    genK n w ctx.chP r.chC r.gens[l]! (wK n w ctx.chN r.nuW)
      (pc n w (wK n w r.chX (r.epsW[l]!)) (wK n w ctx.chN r.nuW)))

@[expose] noncomputable def chainBindK (cd : ChainData) (PS PSI : ℕ → ℕ) (kS nb BP : ℕ)
    (D : List (List ℤ)) : Bool :=
  Nat.beq cd.S.size kS && (List.range kS).all (fun j => arrBind cd.S[j]! n w (PS j)) &&
    Nat.beq cd.base.length nb &&
    (List.range nb).all (fun t => Nat.beq cd.base.toArray[t]! (pg w (mask w) BP t)) &&
    Nat.beq cd.W.size kS && decide (cd.k ≤ kS) && (List.range cd.k).all (fun j => cd.W[j]!.isEmpty) &&
    decide (cd.W.extract cd.k cd.W.size = D.toArray) &&
    (List.range kS).all (fun j => permOK n w (mask w) (n * w) (PS j) (PSI j)) &&
    decide (1 ≤ n) && decide cd.base.Nodup && cd.base.all (fun b => decide (b < n)) &&
    decide (0 < cd.chunks)

abbrev RepOrd := ℕ × ℕ × ℕ

@[expose] noncomputable def fcK (c : FCCert) (oP oN oTN : ℕ) (ro : List RepOrd)
    (bt : ℕ → ℕ → ℕ) : Bool :=
  chainBK n w c.ctx.chP && chainBK n w c.ctx.chN && chainBK n w c.chTN &&
  c.reps.all (fun r => chainBK n w r.chC && chainBK n w r.chX && chainBK n w r.chT) &&
  ctxK n w c.ctx &&
  origsK n w c.chTN c.ctx.chN c.tnW && Nat.beq oTN (2 ^ c.sylA) &&
  Nat.beq oN (2 ^ c.sylA * c.sylM) && decide (c.sylM % 2 = 1) &&
  coverK n w c.chTN c.ctx.chN c.tel c.reps.length (fun j => wK n w c.ctx.chN (c.reps[j - 1]!).nuW)
    oTN &&
  Nat.beq ro.length c.reps.length &&
  (List.range c.reps.length).all (fun j =>
    repK n w c.ctx c.reps[j]! (bt j) oP (ro[j]!).1 (ro[j]!).2.1 (ro[j]!).2.2)

@[expose] noncomputable def letKT (cd : ChainData) (k : ℕ) (PS PSI : ℕ → ℕ) (l : ℤ) : ℕ :=
  if 0 < l then (if l.toNat - 1 < k then PS (l.toNat - 1) else SC w cd (l.toNat - 1))
  else (if (-l).toNat - 1 < k then PSI ((-l).toNat - 1) else SIC n w cd ((-l).toNat - 1))

@[expose] noncomputable def parOKT (L : ℤ → ℕ) (BT : ℕ → ℕ) : ℕ → List (ℕ × ℤ) → Bool
  | _, [] => true
  | m, (p, l) :: rest =>
    Nat.beq (BT (m + 1)) (pc n w (pc n w (L l) (BT p)) (L (-l))) && parOKT L BT (m + 1) rest

@[expose] noncomputable def repKT (ctx : Ctx) (r : RepCert) (BT : ℕ → ℕ) (oP oC oX oT : ℕ)
    (pb hb fb : Bool) : Bool :=
  lettersOK ctx.chN.S.size r.nuW &&
  Nat.beq (pc n w (wK n w ctx.chN r.nuW) (wK n w ctx.chN r.nuW)) (pid n w) &&
  origsK n w r.chC ctx.chP r.cgW &&
  (List.range r.chC.k).all (fun i =>
    Nat.beq (pc n w (wK n w ctx.chN r.nuW) (SC w r.chC i)) (pc n w (SC w r.chC i) (wK n w ctx.chN r.nuW))) &&
  (bfsOK ctx.chP.S.size r.par 1 && r.ord.all (fun m => decide (m < r.par.length + 1)) &&
    Nat.beq (BT 0) (wK n w ctx.chN r.nuW) && pb && hb ||
    bfsOK ctx.chP.S.size r.par 1 && r.ord.all (fun m => decide (m < r.par.length + 1)) && fb) &&
  decide (oP ≤ r.ord.length * oC) &&
  origsK n w r.chX r.chC r.xgW &&
  (List.range r.chC.k).all (fun i => (List.range r.chX.k).all (fun j =>
    lettersOK r.chX.S.size ((r.xnorm[i]!)[j]!) &&
      Nat.beq (pc n w (pc n w (SC w r.chC i) (SC w r.chX j)) (SIC n w r.chC i))
        (wK n w r.chX ((r.xnorm[i]!)[j]!)))) &&
  (List.range r.chC.k).all (fun i => (List.range r.chC.k).all (fun i' =>
    lettersOK r.chX.S.size ((r.xcomm[i]!)[i']!) &&
      Nat.beq (pc n w (pc n w (SC w r.chC i) (SC w r.chC i')) (pc n w (SIC n w r.chC i) (SIC n w r.chC i')))
        (wK n w r.chX ((r.xcomm[i]!)[i']!)))) &&
  origsK n w r.chT r.chX r.tgW && Nat.beq oT (2 ^ r.sylA) && Nat.beq oX (2 ^ r.sylA * r.sylM) &&
  decide (r.sylM % 2 = 1) && r.epsW.all (lettersOK r.chX.S.size) &&
  coverK n w r.chT r.chC r.tel r.epsW.length (fun k => wK n w r.chX (r.epsW[k - 1]!)) oT &&
  decide (r.gens.length = r.epsW.length) &&
  (List.range r.epsW.length).all (fun l =>
    genK n w ctx.chP r.chC r.gens[l]! (wK n w ctx.chN r.nuW)
      (pc n w (wK n w r.chX (r.epsW[l]!)) (wK n w ctx.chN r.nuW)))

theorem parOKT_append (L : ℤ → ℕ) (BT : ℕ → ℕ) : ∀ (m : ℕ) (a b : List (ℕ × ℤ)),
    parOKT n w L BT m (a ++ b) = (parOKT n w L BT m a && parOKT n w L BT (m + a.length) b)
  | m, [], b => by simp [parOKT]
  | m, (p, l) :: a, b => by
    have e : m + 1 + a.length = m + (a.length + 1) := by omega
    simp only [List.cons_append, parOKT, parOKT_append L BT (m + 1) a b, List.length_cons,
      Bool.and_assoc, e]

theorem parOKT_chunks (L : ℤ → ℕ) (BT : ℕ → ℕ) (k : ℕ) : ∀ (c m : ℕ) (l : List (ℕ × ℤ)),
    l.length ≤ c * k →
    (∀ j < c, parOKT n w L BT (m + j * k) ((l.drop (j * k)).take k) = true) →
    parOKT n w L BT m l = true
  | 0, m, l, hl, _ => by
    cases l with
    | nil => rfl
    | cons a l => simp at hl
  | c + 1, m, l, hl, h => by
    have h0 := h 0 (Nat.succ_pos c)
    simp only [Nat.zero_mul, Nat.add_zero, List.drop_zero] at h0
    rw [← List.take_append_drop k l, parOKT_append, h0, Bool.true_and]
    by_cases hk : k ≤ l.length
    · rw [List.length_take_of_le hk]
      refine parOKT_chunks L BT k c (m + k) (l.drop k) ?_ fun j hj => ?_
      · rw [List.length_drop, Nat.succ_mul] at *
        omega
      · have hj1 := h (j + 1) (by omega)
        have e1 : (l.drop k).drop (j * k) = l.drop ((j + 1) * k) := by
          rw [List.drop_drop, Nat.succ_mul, Nat.add_comm]
        have e2 : m + k + j * k = m + (j + 1) * k := by
          rw [Nat.succ_mul]
          omega
        rw [e1, e2]
        exact hj1
    · rw [List.drop_eq_nil_of_le (by omega)]
      rfl

theorem strictInc_split : ∀ (k : ℕ) (l : List ℕ), strictInc (l.take (k + 1)) = true →
    strictInc (l.drop k) = true → strictInc l = true
  | 0, l, _, h2 => by simpa using h2
  | _ + 1, [], _, _ => rfl
  | _ + 1, [_], _, _ => rfl
  | k + 1, a :: b :: t, h1, h2 => by
    simp only [List.take_succ_cons, List.drop_succ_cons, strictInc, Bool.and_eq_true] at h1 h2 ⊢
    exact ⟨h1.1, strictInc_split k (b :: t) (by simpa [List.take_succ_cons] using h1.2) h2⟩

theorem strictInc_chunks (k : ℕ) : ∀ (c : ℕ) (l : List ℕ), l.length ≤ c * k + 1 →
    (∀ j < c, strictInc ((l.drop (j * k)).take (k + 1)) = true) → strictInc l = true
  | 0, [], _, _ => rfl
  | 0, [_], _, _ => rfl
  | 0, _ :: _ :: _, hl, _ => by simp at hl
  | c + 1, l, hl, h => by
    refine strictInc_split k l (by simpa using h 0 (Nat.succ_pos c))
      (strictInc_chunks k c (l.drop k) ?_ fun j hj => ?_)
    · rw [List.length_drop, Nat.succ_mul] at *
      omega
    · have e1 : (l.drop k).drop (j * k) = l.drop ((j + 1) * k) := by
        rw [List.drop_drop, Nat.succ_mul, Nat.add_comm]
      rw [e1]
      exact h (j + 1) (by omega)

theorem letKT_eq (cd : ChainData) (k : ℕ) (PS PSI : ℕ → ℕ)
    (h : (List.range k).all (fun i => Nat.beq (SC w cd i) (PS i) && Nat.beq (SIC n w cd i) (PSI i))
      = true) (l : ℤ) : letK n w cd l = letKT n w cd k PS PSI l := by
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, Nat.beq_eq] at h
  unfold letK letKT
  split_ifs with h1 h2 h3 <;> first | rfl | exact (h _ ‹_›).1 | exact (h _ ‹_›).2

theorem parOKT_eq (cd : ChainData) (BT : ℕ → ℕ) (L : ℤ → ℕ) (hL : ∀ l, letK n w cd l = L l) :
    ∀ m par, parOK n w cd BT m par = parOKT n w L BT m par
  | _, [] => rfl
  | m, (p, l) :: rest => by
    simp only [parOK, parOKT, hL, parOKT_eq cd BT L hL (m + 1) rest]

theorem repKT_eq (ctx : Ctx) (r : RepCert) (BT : ℕ → ℕ) (oP oC oX oT : ℕ) (L : ℤ → ℕ)
    (hL : ∀ l, letK n w ctx.chP l = L l) :
    repK n w ctx r BT oP oC oX oT = repKT n w ctx r BT oP oC oX oT (parOKT n w L BT 0 r.par)
      (strictInc (r.ord.map fun m => hashK n w (BT m)) ||
        strictInc (r.ord.map fun m => ptKeyK n w ctx.chN.base (BT m)))
      (fixOrbK n w ctx.chP (wK n w ctx.chN r.nuW) r.par r.ord BT ||
        relOrbL n w ctx.chP (wK n w ctx.chN r.nuW) ctx.rel ctx.relP ctx.relK r.par r.ord BT) := by
  unfold repK repKT bfsK
  simp only [parOKT_eq n w ctx.chP BT L hL]

theorem repKT_or {ctx : Ctx} {r : RepCert} {BT : ℕ → ℕ} {oP oC oX oT : ℕ} {pb hb fb fb' : Bool}
    (h : repKT n w ctx r BT oP oC oX oT pb hb fb = true) :
    repKT n w ctx r BT oP oC oX oT pb hb (fb || fb') = true := by
  cases fb
  · cases fb'
    · exact h
    · revert h
      unfold repKT
      simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.and_false, Bool.or_false,
        Bool.false_eq_true]
      tauto
  · exact h

theorem imgSetK_append (k : ℕ) (L : ℤ → ℕ) (FT : ℕ → ℕ) : ∀ (m : ℕ) (a b : List (ℕ × ℤ)),
    imgSetK w k L FT m (a ++ b) = (imgSetK w k L FT m a && imgSetK w k L FT (m + a.length) b)
  | m, [], b => by simp [imgSetK]
  | m, (p, l) :: a, b => by
    have e : m + 1 + a.length = m + (a.length + 1) := by omega
    simp only [List.cons_append, imgSetK, imgSetK_append k L FT (m + 1) a b, List.length_cons,
      Bool.and_assoc, e]

theorem imgSetK_chunks (k' : ℕ) (L : ℤ → ℕ) (FT : ℕ → ℕ) (k : ℕ) : ∀ (c m : ℕ) (l : List (ℕ × ℤ)),
    l.length ≤ c * k →
    (∀ j < c, imgSetK w k' L FT (m + j * k) ((l.drop (j * k)).take k) = true) →
    imgSetK w k' L FT m l = true
  | 0, m, l, hl, _ => by
    cases l with
    | nil => rfl
    | cons a l => simp at hl
  | c + 1, m, l, hl, h => by
    have h0 := h 0 (Nat.succ_pos c)
    simp only [Nat.zero_mul, Nat.add_zero, List.drop_zero] at h0
    rw [← List.take_append_drop k l, imgSetK_append, h0, Bool.true_and]
    by_cases hk : k ≤ l.length
    · rw [List.length_take_of_le hk]
      refine imgSetK_chunks k' L FT k c (m + k) (l.drop k) ?_ fun j hj => ?_
      · rw [List.length_drop, Nat.succ_mul] at *
        omega
      · have hj1 := h (j + 1) (by omega)
        have e1 : (l.drop k).drop (j * k) = l.drop ((j + 1) * k) := by
          rw [List.drop_drop, Nat.succ_mul, Nat.add_comm]
        have e2 : m + k + j * k = m + (j + 1) * k := by
          rw [Nat.succ_mul]
          omega
        rw [e1, e2]
        exact hj1
    · rw [List.drop_eq_nil_of_le (by omega)]
      rfl

theorem fixOrbK_of (cd : ChainData) (seed : ℕ) (par : List (ℕ × ℤ)) (ord : List ℕ) (FT : ℕ → ℕ)
    (k : ℕ) (hk : fixNumK n w seed = k) (L : ℤ → ℕ) (hL : ∀ l, letK n w cd l = L l)
    (h1 : (Nat.blt k 4294967296 && Nat.beq (setKeyK w k (FT 0)) (fixBitsK n w seed) &&
      strictInc (ord.map fun m => setKeyK w k (FT m))) = true)
    (h2 : imgSetK w k L FT 0 par = true) : fixOrbK n w cd seed par ord FT = true := by
  have e : letK n w cd = L := funext hL
  unfold fixOrbK
  rw [hk, e]
  simp only [Bool.and_eq_true] at h1 ⊢
  obtain ⟨⟨a, b⟩, c⟩ := h1
  exact ⟨⟨⟨a, b⟩, h2⟩, c⟩

theorem relOrbK_of (cd : ChainData) (seed : ℕ) (R : List ℕ) (kr : ℕ) (RP : ℕ → ℕ) (k : ℕ)
    (par : List (ℕ × ℤ)) (ord : List ℕ) (FT : ℕ → ℕ) (L : ℤ → ℕ) (hL : ∀ l, letK n w cd l = L l)
    (h1 : (Nat.blt k 4294967296 &&
      (List.range n).all (fun a => Nat.beq R[a]! (setKeyK w kr (RP a))) &&
      (List.range cd.k).all (fun i => relMapK n w kr RP (SC w cd i) &&
        relMapK n w kr RP (SIC n w cd i)) &&
      Nat.beq (setKeyK w k (FT 0)) (relBitsK n w kr RP seed) &&
      strictInc (ord.map fun m => setKeyK w k (FT m))) = true)
    (h2 : imgSetK w k L FT 0 par = true) : relOrbK n w cd seed R kr RP k par ord FT = true := by
  have e : letK n w cd = L := funext hL
  unfold relOrbK
  rw [e]
  simp only [Bool.and_eq_true] at h1 ⊢
  obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, f⟩ := h1
  exact ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, h2⟩, f⟩

end CFSG.KC.ExactGen

end
