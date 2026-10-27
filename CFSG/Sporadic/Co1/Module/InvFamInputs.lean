
module

public import CFSG.Sporadic.Co1.Module.InvDataInputs
public import Certificates.Data.Kernel.Co1M.InvFam
public import CFSG.Certificates.Kernel.Co1F2Sound

public section

namespace CFSG.Sporadic.Co1.Module

open CFSG.KC.InvFam CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.SortTree

@[expose] def code4Word : List Bool :=
  invWord "BABABABBABABBABBABABABBABABABABABABBABABABBABABABABABABAB"

structure STree where
  tab : Nat → Nat
  wl : Nat
  wp : Nat
  B : Nat
  C : Nat

@[expose] def STree.OK (act : Nat → Nat → Nat) (ng root wv n : Nat) (T : STree) : Prop :=
  n ≤ T.C * T.B ∧ ∀ c < T.C, chunkOK act ng (fun _ => true) root T.tab n wv T.wl T.wp T.B c = true

structure InvFamW where
  R : List Nat
  RT : List Nat
  P : List (List (Nat × Nat))
  a0 : Nat
  a1 : Nat
  w0 : Nat
  w1 : Nat
  K1 : List Nat
  K2 : List Nat
  K2i : List Nat
  K3 : List Nat
  K3i : List Nat
  K4 : List Nat
  K4i : List Nat
  r1 : List Nat
  r2 : List Nat
  r3 : List Nat
  t1 : STree
  t2 : STree
  t3 : STree
  v1 : STree
  v0 : STree
  uB : Nat
  wB : Nat
  uC : Nat
  wC : Nat
  KB : List Nat
  KC : List Nat
  vb : STree
  vc : STree

@[expose] noncomputable def InvFamW.reg (W : InvFamW) (i : Nat) : Nat := getL 0 W.R i

@[expose] noncomputable def InvFamW.regT (W : InvFamW) (i : Nat) : Nat := getL 0 W.RT i

@[expose] def InvFamW.idxL (W : InvFamW) : List Nat :=
  [7, 9, 11] ++ W.K1 ++ W.K2 ++ W.K2i ++ W.K3 ++ W.K3i ++ W.K4 ++ W.K4i ++ W.r1 ++ W.r2 ++ W.r3 ++
    W.KB ++ W.KC

structure InvFamOK (W : InvFamW) : Prop where
  rA : dat.rowsA = unpackR 24 (W.reg 0)
  rB : dat.rowsB = unpackR 24 (W.reg 1)
  sA : rowsSA = unpackR 24 (W.reg 7)
  sB : rowsSB = unpackR 24 (W.reg 9)
  sC : rowsSC = unpackR 24 (W.reg 11)
  prog : progK 24 W.R W.P 2 = true
  tr : allN (lenL W.R) (fun i => Nat.beq (trK 24 (W.reg i)) (W.regT i)) = true
  idx : bndK (lenL W.R) W.idxL = true
  fix3 : fixAllK W.RT (W.K1 ++ W.K2 ++ W.K3 ++ W.K4 ++
    [getL 0 W.r1 0, getL 0 W.r2 0, getL 0 W.r3 0]) [code3] = true
  fix1 : fixAllK W.RT W.K1 [W.a0] = true
  fix2 : fixAllK W.RT W.K2 [W.a0, W.w0] = true
  fixK3 : fixAllK W.RT W.K3 [W.a0, W.a1] = true
  fix4 : fixAllK W.RT W.K4 [W.a0, W.a1, W.w1] = true
  inv : andB (invPairsK W.R W.K2 W.K2i) (andB (invPairsK W.R W.K3 W.K3i)
    (invPairsK W.R W.K4 W.K4i)) = true
  roots : andB (rootK W.R W.r1 7) (andB (rootK W.R W.r2 7) (rootK W.R W.r3 7)) = true
  rootAct : andB (Nat.beq (vmF 24 (W.regT (getL 0 W.r1 2)) W.a0) W.a0)
    (andB (Nat.beq (vmF 24 (W.regT (getL 0 W.r1 2)) W.a1) W.a1)
    (andB (Nat.beq (vmF 24 (W.regT (getL 0 W.r2 2)) W.a0) W.a0)
    (andB (Nat.beq (vmF 24 (W.regT (getL 0 W.r2 2)) W.a1) W.w1)
      (Nat.beq (vmF 24 (W.regT (getL 0 W.r3 2)) W.a0) W.w0)))) = true
  vecs : bndK (2 ^ 24) [W.a0, W.a1, W.w0, W.w1, W.wB, W.wC] = true
  t1 : W.t1.OK (actC W.R W.K3 W.K3i) (lenL W.K3) (W.reg (getL 0 W.r1 2)) 576 2835
  t2 : W.t2.OK (actC W.R W.K4 W.K4i) (lenL W.K4) (W.reg (getL 0 W.r2 2)) 576 120
  t3 : W.t3.OK (actC W.R W.K2 W.K2i) (lenL W.K2) (W.reg (getL 0 W.r3 2)) 576 540
  v1 : W.v1.OK (actV W.RT W.K3) (lenL W.K3) W.w1 24 162
  v0 : W.v0.OK (actV W.RT W.K1) (lenL W.K1) W.w0 24 275
  mem : andB (notB (memK W.v1.tab 162 24 W.a1)) (notB (memK W.v0.tab 275 24 W.a0)) = true
  fixB : fixAllK W.RT W.KB [code4, W.uB] = true
  fixC : fixAllK W.RT W.KC [code4, W.uC] = true
  img : andB (Nat.beq (vmF 24 (W.regT 9) W.uB) W.wB) (Nat.beq (vmF 24 (W.regT 11) W.uC) W.wC) = true
  vb : W.vb.OK (actV W.RT W.KB) (lenL W.KB) W.wB 24 2000
  vc : W.vc.OK (actV W.RT W.KC) (lenL W.KC) W.wC 24 2000

end CFSG.Sporadic.Co1.Module

end
