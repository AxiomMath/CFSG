module

public import CFSG.Sporadic.Co1.Module.InvFamInputs
public import CFSG.Sporadic.Co1.Module.PairsCheckInputs
public import Certificates.Data.Kernel.Co1M.TwoBK
public import Certificates.Data.Kernel.Co1M.Syl64

@[expose] public section

namespace CFSG.Sporadic.Co1.Module.Co2Stab

open CFSG.Sporadic.SmallF2.Native CFSG.KC.InvFam CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT
  CFSG.KC.Co1M CFSG.KC.XorSel CFSG.KC.Syl64 CFSG.Sporadic.Co1.Module

def inO64 (w : ℕ) : Bool :=
  Pairs.inPts (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 w

def emptyT64 : STree := ⟨fun _ => 0, 0, 0, 0, 0⟩

structure SylW where
  R : List ℕ
  RT : List ℕ
  P : List (List (ℕ × ℕ))
  SI : List ℕ
  GI : ℕ
  GJ : ℕ
  RS : List ℕ
  RST : List ℕ
  PS : List (List (ℕ × ℕ))
  Q : ℕ
  QI : ℕ
  BASE : List ℕ
  LV : List (List ℕ)
  SZ : List ℕ
  T : List STree
  E : List ℕ
  CN : List ℕ
  CM : List (List ℕ)
  L : List ℕ
  CL : List ℕ
  CLG : List ℕ
  PVL : List ℕ
  PP : List ℕ
  CP : List ℕ
  PVP : List ℕ
  U : List ℕ

noncomputable def SylW.E2 (W : SylW) : List ℕ := conjL (getL 0 W.R W.GI) (getL 0 W.R W.GJ) W.E

structure SylOK (W : SylW) : Prop where
  rA : dat.rowsA = unpackR 24 (getL 0 W.R 0)
  rB : dat.rowsB = unpackR 24 (getL 0 W.R 1)
  prog : progK 24 W.R W.P 2 = true
  tr : allN (lenL W.R) (fun i => Nat.beq (trK 24 (getL 0 W.R i)) (getL 0 W.RT i)) = true
  lenSI : lenL W.SI = 5
  idx : bndK (lenL W.R) (W.GI :: W.GJ :: W.SI) = true
  fix : fixAllK W.RT (W.GI :: W.SI) [2] = true
  ginv : mulF 24 (getL 0 W.R W.GI) (getL 0 W.R W.GJ) = idF 24
  seed : allN 5 (fun k => Nat.beq (getL 0 W.RS k) (getL 0 W.R (getL 0 W.SI k))) = true
  progS : progK 24 W.RS W.PS 5 = true
  trS : allN (lenL W.RS) (fun i => Nat.beq (trK 24 (getL 0 W.RS i)) (getL 0 W.RST i)) = true
  flag : mulF 24 W.Q W.QI = idF 24 ∧ mulF 24 W.QI W.Q = idF 24
  uni : allN 5 (fun k => uniK (mulF 24 (mulF 24 W.Q (getL 0 W.RS k)) W.QI)) = true
  lenLV : W.LV.length = W.BASE.length
  idxS : bndK (lenL W.RS) W.LV.flatten = true
  base : bndK (2 ^ 24) W.BASE = true
  cfix : ∀ j < W.BASE.length, fixAllK W.RST (W.LV.getD j []) (W.BASE.take j) = true
  tree : ∀ j < W.BASE.length, (W.T.getD j emptyT64).OK (actV W.RST (W.LV.getD j []))
    (lenL (W.LV.getD j [])) (W.BASE.getD j 0) 24 (W.SZ.getD j 0)
  prod : 2 ^ 18 ≤ ((List.range W.BASE.length).map fun j => W.SZ.getD j 0).prod
  cn : allN 5 (fun k => Nat.beq (Nat.xor (getL 0 W.RS k) (idF 24)) (selK W.E (getL 0 W.CN k))) =
    true
  cm : ∀ k < 5, selAllK W.E (mulL W.E (Nat.xor (getL 0 W.RS k) (idF 24))) (W.CM.getD k []) = true
  cl : selAllK W.E W.L W.CL = true
  clg : selAllK W.E2 W.L W.CLG = true
  cp : selAllK (W.E ++ W.E2) W.PP W.CP = true
  pvl : pivOK 576 W.L W.PVL = true
  pvp : pivOK 576 W.PP W.PVP = true
  dim : W.E.length + W.E2.length ≤ W.PP.length + W.L.length
  wit : witK inO64 W.L W.U = true

end CFSG.Sporadic.Co1.Module.Co2Stab

end
