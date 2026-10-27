module

public import CFSG.Sporadic.Co1.Module.InvFamInputs
public import Certificates.Data.Kernel.Co1M.U6Odd
public import Certificates.Data.Kernel.Co1M.U6OddLab
public import Certificates.Data.Kernel.Co1FixList
public import CFSG.Assembly.Defs
public import CFSG.Sporadic.Co1.Module.PairsCheckInputs
public import Certificates.Data.CFSGNative.Co1.U6OddData

@[expose] public section

namespace CFSG.Sporadic.Co1.Module.U6Odd

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.OddNative CFSG.Sporadic.Co1.U6OddNative
  CFSG.KC.InvFam CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.SortTree CFSG.KC.U6Odd
  CFSG.KC.Co1Fix CFSG.Sporadic.Co1.Module

def labU6 : ℕ → ℕ :=
  Pairs.tyLab (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280

def s0ord : List ℕ := [9, 3, 3]

def nilT : STree := ⟨fun _ => 0, 0, 0, 0, 0⟩

structure PrimeW where
  F : List ℕ
  Y : List ℕ
  W : List ℕ
  PV : List ℕ
  LB : ℕ
  T : List STree

structure U6W where
  R : List ℕ
  RT : List ℕ
  X : List ℕ
  w11 : PrimeW
  w7 : PrimeW
  w5 : PrimeW
  cl11 : STree
  n5 : STree
  s0 : STree
  e0 : ℕ → ℕ
  c0 : ℕ → ℕ

noncomputable def U6W.reg (W : U6W) (i : ℕ) : ℕ := getL 0 W.R i

noncomputable def U6W.regT (W : U6W) (i : ℕ) : ℕ := getL 0 W.RT i

noncomputable def U6W.s0v (W : U6W) (i : ℕ) : ℕ := valF 576 (W.s0.tab i)

structure PrimeOK (W : U6W) (pd : PrimeData) (P : PrimeW) : Prop where
  lenLv : pd.lv.length = pd.base.length
  lenSz : pd.sz.length = pd.base.length
  idx : bndK (lenL W.R) (pd.g :: pd.lv.flatten) = true
  base : bndK (2 ^ 24) pd.base = true
  fix : ∀ i < pd.base.length, fixAllK W.RT (pd.lv.getD i []) (u1 :: u2 :: pd.base.take i) = true
  tree : ∀ i < pd.base.length, (P.T.getD i nilT).OK (actV W.RT (pd.lv.getD i []))
    (lenL (pd.lv.getD i [])) (pd.base.getD i 0) 24 (pd.sz.getD i 0)
  prod : 9196830720 ≤ ((List.range pd.base.length).map fun i => pd.sz.getD i 0).prod * pd.k
  prime : pd.p.Prime
  gpow : powK 24 (W.reg pd.g) pd.p = idF 24
  gne : W.reg pd.g ≠ idF 24
  gcanon : canonK (W.reg pd.g) = W.reg pd.g
  gfix : fixAllK W.RT [pd.g] (u1 :: u2 :: pd.base) = true
  fixc : fixK 24 (W.regT pd.g) 0 P.F P.Y (lenL P.F) (pw2 (lenL P.F)) 0 = true
  fixl : fixListK (W.regT pd.g) (W.regT pd.g) P.F P.W = true
  shape : pd.b.take (2 + pd.base.length) = u1 :: u2 :: pd.base
  blt : bndK (2 ^ 24) pd.b = true
  bfix : fixAllK W.RT [pd.g] pd.b = true
  labT : labCK labU6 P.PV P.LB P.W = true
  tup : tupK (labC P.PV P.LB) P.W u1 u2 pd.b pd.t = true

structure U6OK (W : U6W) : Prop where
  rA : dat.rowsA = unpackR 24 (W.reg 0)
  rB : dat.rowsB = unpackR 24 (W.reg 1)
  prog : progK 24 W.R prog 2 = true
  tr : allN (lenL W.R) (fun i => Nat.beq (trK 24 (W.reg i)) (W.regT i)) = true
  p11 : PrimeOK W data11 W.w11
  p7 : PrimeOK W data7 W.w7
  p5 : PrimeOK W data5 W.w5
  clIdx : bndK (lenL W.R) cls11 = true
  clFix : fixAllK W.RT cls11 (u1 :: u2 :: data11.base) = true
  clInv : allN 2 (fun l => Nat.beq (mulF 24 (W.reg (getL 0 cls11 l)) (getL 0 W.X l)) (idF 24)) = true
  clLen : lenL cls11 = 2
  clCanon : canonK (W.reg data11.g) = W.reg data11.g
  cl : W.cl11.OK (actH (cls11.map W.reg) W.X) 2 (W.reg data11.g) 576 60
  nIdx : bndK (lenL W.R) nrm5 = true
  nLen : lenL nrm5 = 2
  nFix : fixAllK W.RT nrm5 [u1, u2] = true
  nNorm : allL nrm5 (fun x => normK (W.reg x) (W.reg data5.g) 5) = true
  nT : W.n5.OK (actR (nrm5.map W.reg)) 2 (idF 24) 576 120
  sIdx : bndK (lenL W.R) s0gens = true
  sLen : lenL s0gens = 3
  sFix : fixAllK W.RT s0gens [u1, u2] = true
  sOrd : allN 3 (fun l => Nat.beq (powK 24 (W.reg (getL 0 s0gens l)) (getL 0 s0ord l)) (idF 24)) = true
  sT : W.s0.OK (actR (s0gens.map W.reg)) 3 (idF 24) 576 729
  sC : closeOK (actR (s0gens.map W.reg)) 3 W.s0.tab (fun i k => fget (W.e0 i) k 10) 729 576
    W.s0.B W.s0.C = true
  sW : allN 729 (fun i => witK W.s0v 729 i (W.c0 i)) = true
  sB : zerosK 729 W.c0 ≤ 27
  l2 : labU6 u2 = 3
  l12 : labU6 (u1 ^^^ u2) = 3

end CFSG.Sporadic.Co1.Module.U6Odd

end
