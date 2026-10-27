module

public import Certificates.Data.Kernel.SporLatDc2

public noncomputable section

namespace CFSG.KC.SLD2

open CFSG.KC.E64F CFSG.KC.LQT.PW
open CFSG.KC.SLDc (labF wordE sortedLt sumN cntB anyB takeN allIdx all2 headL pairF lookC
  chunksOK)

section Checks

variable (C : Dc2Ctx) (D : Dc2Data)

@[expose] def isS (w : List Nat) : Bool := w.all fun l => Nat.blt l C.ns

@[expose] def isF (w : List Nat) : Bool := w.all fun l => Nat.blt l C.nf

@[expose] def isW (w : List Nat) : Bool := w.all fun l => Nat.blt l C.nl

@[expose] def lw (w x : List Nat) : List Nat := labF (wordF C.L w) x

@[expose] def inO (b : BOrb) (p : Nat) : Bool := Nat.beq (imgW 1 b.omc p) 1

@[expose] def tl (b : BOrb) (p : Nat) : Nat := imgW D.pw b.tlc p

@[expose] def dp (b : BOrb) (p : Nat) : Nat := imgW D.pw b.dpc p

@[expose] def pathW (b : BOrb) : Nat → Nat → List Nat → List Nat
  | 0, _, acc => acc
  | f + 1, q, acc =>
    bif Nat.blt (tl D b q) C.ns then pathW b f (C.L (tl D b q) q) (tl D b q :: acc) else acc

@[expose] def ptOK (b : BOrb) (p : Nat) : Bool :=
  !inO b p || ((List.range C.ns).all (fun l => inO b (C.L l p)) &&
    (Nat.beq p b.qs || (Nat.blt (tl D b p) C.ns && inO b (C.L (tl D b p) p) &&
      Nat.beq (Nat.succ (dp D b (C.L (tl D b p) p))) (dp D b p))))

@[expose] def borbOK (b : BOrb) : Bool :=
  (List.range C.n).all (ptOK C D b) && Nat.blt b.qs C.n && inO b b.qs &&
    Nat.beq (cntB (inO b) (List.range C.n)) b.osz &&
    b.kg.all (fun w => isS C w && Nat.beq (wordF C.L w b.qs) b.qs) &&
    b.kw.all (fun u => u.all fun i => Nat.blt i b.kg.length) &&
    sortedLt (b.kw.map fun u => D.sep.map (wordE C.L b.kg u)) &&
    Nat.beq (Nat.mul b.kw.length b.osz) (2 ^ C.k)

@[expose] def sLet : List (List Nat) := (List.range C.ns).map fun l => [l]

@[expose] def clRow (Cl : Clos) (j : Nat) : List Nat :=
  (List.range Cl.C.flatten.length).map (imgW D.pw (Cl.rows.getD j 0))

@[expose] def clOK (G : List (List Nat)) (x : List Nat) (P : List Nat → Bool) (Cl : Clos) : Bool :=
  chunksOK Cl.B Cl.C && Nat.ble Cl.R.length Cl.C.flatten.length &&
    all2 (fun w y => isS C w && y == lw C w x && P y) Cl.R (takeN Cl.R.length Cl.C.flatten) &&
    (List.range G.length).all (fun j => (List.zip (clRow D Cl j) Cl.C.flatten).all fun e =>
      Nat.blt e.1 Cl.C.flatten.length && lookC Cl.B Cl.C e.1 == lw C (G.getD j []) e.2) &&
    Nat.beq Cl.par.length Cl.C.flatten.length && Nat.beq Cl.via.length Cl.C.flatten.length &&
    allIdx (fun i e => Nat.blt i Cl.R.length || (Nat.blt e.1 i && Nat.blt e.2 G.length &&
      Nat.beq (imgW D.pw (Cl.rows.getD e.2 0) e.1) i)) 0 (List.zip Cl.par Cl.via) &&
    Nat.beq Cl.ord.length Cl.C.flatten.length &&
    Cl.ord.all (fun i => Nat.blt i Cl.C.flatten.length) && sortedLt (Cl.ord.map (lookC Cl.B Cl.C))

@[expose] def atOK (Cl : Clos) (x w : List Nat) (i : Nat) : Bool :=
  Nat.blt i Cl.C.flatten.length && lookC Cl.B Cl.C i == lw C w x

@[expose] def missOK (x : List Nat) (i : Nat) : Bool :=
  (List.range i).all fun j => Nat.beq (cntB (inO (D.bo.getD j default)) x) 0

@[expose] def modeEOK (x : List Nat) (m : Nat) (Cl : Clos) : Bool :=
  missOK D x D.bo.length && clOK C D (sLet C) x (fun _ => true) Cl &&
    Nat.beq m Cl.C.flatten.length

@[expose] def modeBOK (i : Nat) (b : BOrb) (x : List Nat) (m : Nat) (Cl : Clos) : Bool :=
  Nat.blt i D.bo.length && missOK D x i && Nat.blt 0 (cntB (inO b) x) &&
    clOK C D b.kg x (fun y => anyB (Nat.beq b.qs) y) Cl &&
    all2 (fun q j => isS C (pathW C D b 64 q []) &&
      Nat.beq (wordF C.L (pathW C D b 64 q []) q) b.qs &&
      atOK C Cl x (pathW C D b 64 q []) j) (x.filter (inO b)) Cl.si &&
    Nat.beq (Nat.mul m (cntB (inO b) x)) (Nat.mul b.osz Cl.C.flatten.length)

@[expose] def rec1OK (r : Rec1) : Bool :=
  isW C r.u && r.key == r.mode :: headL (r.cl.ord.map (lookC r.cl.B r.cl.C)) &&
    bif Nat.beq r.mode 0 then modeEOK C D (lw C r.u C.Λ) r.m r.cl
    else modeBOK C D (Nat.pred r.mode) (D.bo.getD (Nat.pred r.mode) default) (lw C r.u C.Λ) r.m r.cl

@[expose] def fAct (l : Nat) (x : List Nat) : List Nat :=
  labF (clampF (Nat.mul C.n C.n) (pairF C.n (C.L l))) x

@[expose] def fRow (l : Nat) : List Nat := (List.range C.N2).map (imgW D.fw (D.fpc.getD l 0))

@[expose] def fRowOK (l : Nat) : Bool :=
  (List.zip (fRow C D l) D.fC.flatten).all fun e =>
    Nat.blt e.1 C.N2 && lookC D.fB D.fC e.1 == fAct C l e.2

@[expose] def fRestOK : Bool :=
  chunksOK D.fB D.fC && (D.fC.flatten.headD [] == C.Δ) && Nat.beq D.fC.flatten.length C.N2 &&
    Nat.beq D.fpar.length C.N2 && Nat.beq D.fvia.length C.N2 &&
    allIdx (fun i e => Nat.beq i 0 || (Nat.blt e.1 i && Nat.blt e.2 C.nf &&
      Nat.beq (imgW D.fw (D.fpc.getD e.2 0) e.1) i)) 0 (List.zip D.fpar D.fvia) &&
    Nat.beq D.ford.length C.N2 && D.ford.all (fun i => Nat.blt i C.N2) &&
    sortedLt (D.ford.map (lookC D.fB D.fC))

@[expose] def idxW (w : List Nat) (i : Nat) : Nat :=
  w.foldr (fun l j => imgW D.fw (D.fpc.getD l 0) j) i

@[expose] def fdep (fc i : Nat) : Nat := Nat.mod (imgW D.gw fc i) D.gd

@[expose] def fgen (fc i : Nat) : Nat := Nat.div (imgW D.gw fc i) D.gd

@[expose] def lev2OK (u : List Nat) (e : Rec2) : Bool :=
  e.1.all (fun ts => isF C ts.1 && isS C ts.2 &&
    D.sep.all fun p => Nat.beq (wordF C.L (u ++ ts.1) p) (wordF C.L (ts.2 ++ u) p)) &&
    (List.range C.N2).all (fun i => Nat.beq (fdep D e.2 i) 0 ||
      (Nat.blt (fgen D e.2 i) e.1.length && Nat.beq
        (Nat.succ (fdep D e.2 (idxW D (e.1.getD (fgen D e.2 i) default).1 i))) (fdep D e.2 i)))

@[expose] def rec2OK (c : Nat) : Bool := lev2OK C D (D.R1.getD c default).u (D.R2.getD c default)

@[expose] def dep0 (c : Nat) : List (Nat × Nat) :=
  ((List.range C.N2).filter fun i => Nat.beq (fdep D (D.R2.getD c default).2 i) 0).map fun i =>
    (c, i)

@[expose] def rootIdxOK : Bool :=
  D.roots.flatten.map (fun t => (t.c, t.ρ)) == (List.range D.R1.length).flatMap (dep0 C D)

@[expose] def witOK (r : List Nat) (ss : List (List Nat)) (l p : Nat) : Bool :=
  r.isEmpty || (ss.all (isS C) && Nat.blt p C.n && Nat.beq (Nat.mod l 3) 0 &&
    Nat.beq (itW C.L (witW r ss) l p) p && !Nat.beq (itW C.L (witW r ss) (Nat.div l 3) p) p)

@[expose] def rootOK (t : Root) : Bool :=
  isF C t.φ && Nat.beq (idxW D t.φ 0) t.ρ && witOK C ((D.R1.getD t.c default).u ++ t.φ) t.s t.l t.p

@[expose] def rootsOK (b : Nat) : Bool := (D.roots.getD b []).all (rootOK C D)

@[expose] def globOK : Bool :=
  (C.Λ.all fun p => Nat.blt p C.n) && decide (C.Λ.Pairwise (· < ·)) &&
    (C.Δ.all fun p => Nat.blt p (Nat.mul C.n C.n)) && decide (C.Δ.Pairwise (· < ·)) &&
    Nat.ble C.ns C.nf && Nat.ble C.nf C.nl &&
    (List.range C.nf).all (fun l => labF (C.L l) C.Λ == C.Λ) &&
    (List.range C.ns).all (fun l => labF (pairF C.n (C.L l)) C.Δ == C.Δ) &&
    (D.sep.all fun p => Nat.blt p C.n) &&
    sortedLt (D.R1.map Rec1.key) && Nat.beq (sumN (D.R1.map Rec1.m)) C.N1

@[expose] def dc2Check : Bool :=
  globOK C D && (List.range D.bo.length).all (fun i => borbOK C D (D.bo.getD i default)) &&
    (List.range D.R1.length).all (fun c => rec1OK C D (D.R1.getD c default)) &&
    fRestOK C D && (List.range C.nf).all (fRowOK C D) &&
    (List.range D.R1.length).all (rec2OK C D) && (List.range D.roots.length).all (rootsOK C D) &&
    rootIdxOK C D

end Checks

end CFSG.KC.SLD2

end
