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
  (List.range n).foldl (fun h i => (h * 1000003 + pg w (mask w) p i) % 2305843009213693951) 7

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

@[expose] noncomputable def bfsK (cd : ChainData) (seed : ℕ) (par : List (ℕ × ℤ)) (ord : List ℕ)
    (BT : ℕ → ℕ) : Bool :=
  bfsOK cd.S.size par 1 && ord.all (fun m => decide (m < par.length + 1)) &&
    Nat.beq (BT 0) seed && parOK n w cd BT 0 par &&
    strictInc (ord.map fun m => hashK n w (BT m))

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
  bfsK n w ctx.chP (wK n w ctx.chN r.nuW) r.par r.ord BT && decide (oP ≤ r.ord.length * oC) &&
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

end CFSG.KC.ExactGen

end
