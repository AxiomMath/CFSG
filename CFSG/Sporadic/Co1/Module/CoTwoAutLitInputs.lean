module

public import CFSG.Sporadic.Co1.Module.InvFamInputs
public import CFSG.Sporadic.Co1.Module.PairsCheckInputs
public import Certificates.Data.Kernel.Co1M.CoTwoAut66
public import Certificates.Data.Kernel.Co1M.TwoBK
public import CFSG.Assembly.Defs

@[expose] public section

namespace CFSG.Sporadic.Co1.Module.CoTwoAut

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.OddNative CFSG.KC.InvFam CFSG.KC.Co1F2
  CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.SortTree CFSG.KC.CoTwoAut CFSG.KC.Co1M CFSG.Sporadic.Co1.Module

def labA : ℕ → ℕ :=
  Pairs.tyLab (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280

def nilA : STree := ⟨fun _ => 0, 0, 0, 0, 0⟩

structure ForestOK (GT : List ℕ) (T : List STree) (Rt Sz : List ℕ) (P : ℕ → ℕ) (bound : ℕ)
    (ex : ℕ → Bool) : Prop where
  lenT : T.length = Sz.length
  lenR : Rt.length = Sz.length
  roots : bndK (2 ^ 24) Rt = true
  trees : ∀ j < Sz.length, (T.getD j nilA).OK (actV GT [0, 1]) 2 (Rt.getD j 0) 24 (Sz.getD j 0)
  big : ∀ j < Sz.length, bound ≤ Sz.getD j 0 ∨ ex (Rt.getD j 0) = true
  cov : ∀ i < 98280, covAt (T.map STree.tab) Sz P (fun i => (orbitOf 2 98280).pts[i]!) 98280 i = true

structure AutW where
  R0 : ℕ
  R1 : ℕ
  W3 : List (List ℕ)
  W4 : List (List ℕ)
  G3 : List ℕ
  GT3 : List ℕ
  G4 : List ℕ
  GT4 : List ℕ
  T3 : List STree
  Rt3 : List ℕ
  Sz3 : List ℕ
  P3 : ℕ → ℕ
  T4 : List STree
  Rt4 : List ℕ
  Sz4 : List ℕ
  P4 : ℕ → ℕ

def ex3 (r : ℕ) : Bool := bilN (transposeRows 24 f0Rows) r code3

def ex4 (r : ℕ) : Bool := bilN (transposeRows 24 f0Rows) r code4 || labA (r ^^^ code4) == 3

structure AutOK (D : AutW) : Prop where
  rA : dat.rowsA = unpackR 24 D.R0
  rB : dat.rowsB = unpackR 24 D.R1
  lenW : D.W3.length = 2 ∧ D.W4.length = 2 ∧ lenL D.G3 = 2 ∧ lenL D.G4 = 2
  letters : ∀ w ∈ D.W3 ++ D.W4, ∀ l ∈ w, l < 2
  words3 : ∀ l < 2, wK [D.R0, D.R1] (D.W3.getD l []) = getL 0 D.G3 l
  words4 : ∀ l < 2, wK [D.R0, D.R1] (D.W4.getD l []) = getL 0 D.G4 l
  tr3 : ∀ l < 2, trK 24 (getL 0 D.G3 l) = getL 0 D.GT3 l
  tr4 : ∀ l < 2, trK 24 (getL 0 D.G4 l) = getL 0 D.GT4 l
  fix3 : ∀ l < 2, vmF 24 (getL 0 D.GT3 l) code3 = code3
  fix4 : ∀ l < 2, vmF 24 (getL 0 D.GT4 l) code4 = code4
  f3 : ForestOK D.GT3 D.T3 D.Rt3 D.Sz3 D.P3 546 ex3
  f4 : ForestOK D.GT4 D.T4 D.Rt4 D.Sz4 D.P4 553 ex4
  l3 : labA code3 = 2
  l4 : labA code4 = 1

end CFSG.Sporadic.Co1.Module.CoTwoAut

end
