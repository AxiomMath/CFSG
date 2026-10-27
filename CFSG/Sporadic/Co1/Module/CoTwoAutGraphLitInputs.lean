module

public import CFSG.Sporadic.Co1.Module.PairsCheckInputs
public import CFSG.Sporadic.Co2Cert.Lit
public import Certificates.Data.Kernel.Co1M.Graph65
public import Certificates.Data.Kernel.Co1M.Vtx10065
public import CFSG.Certificates.Kernel.Co1F2Sound

@[expose] public section

namespace CFSG.Sporadic.Co1.Module.CoTwoAut

open CFSG.Sporadic.SmallF2.Native CFSG.KC.InvFam CFSG.KC.Co1F2
  CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.SortTree CFSG.KC.Graph65 CFSG.Sporadic.Co1.Module

noncomputable def vtxK (x : ℕ) : ℕ := recT CFSG.KD.Co1M.vtxL65 6 24 x

def inO (w : ℕ) : Bool :=
  Pairs.inPts (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 w

def labG : ℕ → ℕ :=
  Pairs.tyLab (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280

structure GraphW where
  R : List ℕ
  RT : List ℕ
  P : List (List (ℕ × ℕ))
  G : List ℕ
  KS : ℕ → ℕ

structure GraphOK (W : GraphW) : Prop where
  rA : dat.rowsA = unpackR 24 (getL 0 W.R 0)
  rB : dat.rowsB = unpackR 24 (getL 0 W.R 1)
  prog : progK 24 W.R W.P 2 = true
  tr : allN (lenL W.R) (fun i => Nat.beq (trK 24 (getL 0 W.R i)) (getL 0 W.RT i)) = true
  lenG : lenL W.G = 2
  idx : bndK (lenL W.R) W.G = true
  fix : fixAllK W.RT W.G [2] = true
  len : lenL CFSG.Sporadic.Co2Cert.co2G0 = 2300 ∧ lenL CFSG.Sporadic.Co2Cert.co2G1 = 2300
  eqv0 : eqvK (getL 0 W.RT (getL 0 W.G 0)) vtxK 2300 CFSG.Sporadic.Co2Cert.co2G0 0 = true
  eqv1 : eqvK (getL 0 W.RT (getL 0 W.G 1)) vtxK 2300 CFSG.Sporadic.Co2Cert.co2G1 0 = true
  vert : vertK inO vtxK 2300 = true
  dist : sortK vtxK W.KS 2300 = true
  adj3 : adjB labG (Nat.xor (vtxK 0) (vtxK 3)) = true
  adj1 : adjB labG (Nat.xor (vtxK 0) (vtxK 1)) = false

end CFSG.Sporadic.Co1.Module.CoTwoAut

end
