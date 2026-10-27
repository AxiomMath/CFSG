module

public import Certificates.Data.Kernel.Census.PackedBase

public section

namespace CFSG.KC.Census

section Perf

variable (w h : Nat) (L : Nat → Nat)

@[expose] noncomputable def gPt (pc : List (List Nat × List Nat)) (t p : Nat) : Nat :=
  bif Nat.blt t pc.length then commPt w h L (pc.getD t ([], [])).1 (pc.getD t ([], [])).2 p
  else commPt w h L (pc.getD (Nat.sub t pc.length) ([], [])).2
    (pc.getD (Nat.sub t pc.length) ([], [])).1 p

@[expose] noncomputable def gwPt (pc : List (List Nat × List Nat)) : List Nat → Nat → Nat
  | [], p => p
  | t :: l, p => gPt w h L pc t (gwPt pc l p)

@[expose] noncomputable def gwInvPt (pc : List (List Nat × List Nat)) : List Nat → Nat → Nat
  | [], p => p
  | t :: l, p => gwInvPt pc l (gPt w h L pc (lsw pc.length t) p)

@[expose] noncomputable def cgPt (pc : List (List Nat × List Nat)) :
    List (List Nat × List Nat) → Nat → Nat
  | [], p => p
  | uv :: l, p => gwPt w h L pc uv.1 (gwPt w h L pc uv.2
      (gwInvPt w h L pc uv.1 (gwInvPt w h L pc uv.2 (cgPt pc l p))))

@[expose] noncomputable def cjPt (pc : List (List Nat × List Nat)) (y : List Nat) :
    List (List Nat) → Nat → Nat
  | [], p => p
  | q :: l, p => gwPt w h L pc q (gwPt w h L pc y (gwPt w h L pc y
      (gwInvPt w h L pc q (cjPt pc y l p))))

@[expose] noncomputable def perfB (bs : List Nat) (xw : List (List Nat)) (mx : Nat)
    (pc : List (List Nat × List Nat)) (prel : List (List (List Nat × List Nat)))
    (py : List Nat) (pk : Nat) (pcj : List (List (List Nat))) : Bool :=
  pc.all (fun c => c.1.all (fun k => Nat.blt k (2 * h)) && c.2.all (fun k => Nat.blt k (2 * h)) &&
      bs.all (fun b => Nat.beq (wPt w L c.1 (pcwPt w L xw mx b)) (pcwPt w L xw mx (wPt w L c.1 b))) &&
      bs.all (fun b => Nat.beq (wPt w L c.2 (pcwPt w L xw mx b)) (pcwPt w L xw mx (wPt w L c.2 b)))) &&
    Nat.beq prel.length pc.length && Nat.beq pcj.length pc.length &&
    prel.all (fun rl => rl.all fun uv => uv.1.all (fun t => Nat.blt t (2 * pc.length)) &&
      uv.2.all (fun t => Nat.blt t (2 * pc.length))) &&
    py.all (fun t => Nat.blt t (2 * pc.length)) &&
    pcj.all (fun ql => ql.all fun q => q.all fun t => Nat.blt t (2 * pc.length)) &&
    (List.range pc.length).all (fun t => bs.all fun b =>
      Nat.beq (gPt w h L pc t b) (cgPt w h L pc (prel.getD t []) b)) &&
    bs.all (fun b => Nat.beq (iterPt (gwPt w h L pc py) (2 ^ pk) b) b) &&
    (List.range pc.length).all (fun t => bs.all fun b =>
      Nat.beq (gPt w h L pc t b) (cjPt w h L pc py (pcj.getD t []) b))

end Perf

deriving instance Inhabited for ConjDataP

structure RootR where
  d : ConjDataP
  ps : List Nat
  O : Nat
  ix : Nat
  xw : List (List Nat)
  mx : Nat
  mb : List Nat
  mxb : List Nat
  wits : List (Nat × Nat × List (Nat × List Nat × List Nat) × Nat)
  skips : List (Nat × Nat × List Nat × Nat)
  selfs : List Nat
  perfs : List (Nat × Nat)
  pc : List (List Nat × List Nat)
  prel : List (List (List Nat × List Nat))
  py : List Nat
  pk : Nat
  pcj : List (List (List Nat))
deriving Inhabited

section Root

variable (w h : Nat) (L : Nat → Nat) (bs : List Nat)

@[expose] noncomputable def rootXR (px : Nat) (r : RootR) : Bool :=
  bs.all (fun b => Nat.beq (pcwPt w L r.xw r.mx b) (at' w px b)) &&
    bs.any (fun b => !(Nat.beq (pcwPt w L r.xw r.mx b) b)) &&
    r.xw.all (fun x => bs.all fun b =>
      Nat.beq (pcwPt w L r.xw r.mx (wPt w L x b)) (wPt w L x (pcwPt w L r.xw r.mx b)))

@[expose] def inPair (r : RootR) (j e : Nat) : Bool :=
  Nat.beq e r.mx || Nat.beq e (r.mb.getD j 0) || Nat.beq e (r.mxb.getD j 0)

@[expose] noncomputable def rootLeafR (pxs : List Nat) (i : Nat) (r : RootR) : Bool :=
  (List.range r.d.nodes.size).all (fun j => Nat.beq (r.mb.getD j 0) r.mx ||
    r.wits.any (fun t => Nat.beq t.1 j) || r.skips.any (fun s => Nat.beq s.1 j) ||
    r.perfs.any (fun f => Nat.beq f.1 j)) &&
  r.wits.all (fun t => inPair r t.1 t.2.1 &&
    t.2.2.1.all (fun f => inPair r t.1 f.1 && f.2.1.all (fun k => Nat.blt k (2 * h)) &&
      f.2.2.all (fun k => Nat.blt k (2 * h))) &&
    witB w h L bs r.xw t.2.1 t.2.2.1 t.2.2.2) &&
  r.skips.all (fun s => (Nat.beq s.2.1 (r.mb.getD s.1 0) || Nat.beq s.2.1 (r.mxb.getD s.1 0)) &&
    Nat.blt s.2.2.2 i && s.2.2.1.all (fun k => Nat.blt k (2 * h)) &&
    bs.all (fun b => Nat.beq (wPt w L s.2.2.1 (pcwPt w L r.xw s.2.1 b))
      (at' w (pxs.getD s.2.2.2 0) (wPt w L s.2.2.1 b)))) &&
  r.perfs.all (fun f => Nat.blt f.2 r.pc.length &&
    bs.any (fun b => !(Nat.beq (pcwPt w L r.xw (r.mb.getD f.1 0) (gPt w h L r.pc f.2 b))
      (gPt w h L r.pc f.2 (pcwPt w L r.xw (r.mb.getD f.1 0) b))))) &&
  (r.perfs.isEmpty || perfB w h L bs r.xw r.mx r.pc r.prel r.py r.pk r.pcj)

end Root

end CFSG.KC.Census

end
