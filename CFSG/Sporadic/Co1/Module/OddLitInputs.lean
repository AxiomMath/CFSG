
module

public import CFSG.Sporadic.Co1.Module.InvFamInputs
public import Certificates.Data.Kernel.Co1M.Odd73F
public import CFSG.Sporadic.Co1.Module.OddProg

@[expose] public section

namespace CFSG.Sporadic.Co1.Module.Odd

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.OddNative CFSG.KC.InvFam CFSG.KC.Co1F2
  CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.SortTree CFSG.KC.Odd73 CFSG.KD.Co1Odd CFSG.Sporadic.Co1.Module

structure OddW where
  R : List ℕ
  P : List (List (ℕ × ℕ))
  T : STree
  aux : ℕ → ℕ
  Z0G : List ℕ
  Z0P : List ℕ
  Z0Par : List ℕ
  Z0Lab : List ℕ
  V1 : List ℕ
  V2 : List ℕ
  t1i : ℕ

noncomputable def OddW.reg (W : OddW) (i : ℕ) : ℕ := getL 0 W.R i

def nS : ℕ := 182919

structure OddOK (W : OddW) : Prop where
  rA : dat.rowsA = unpackR 24 (W.reg 0)
  rB : dat.rowsB = unpackR 24 (W.reg 1)
  progEq : W.P = prog
  prog : progK 24 W.R W.P 2 = true
  len : lenL W.R = 94
  canon : canonL W.R = true
  tree : W.T.OK (act73 W.R) 14 (W.reg 27) 576 nS
  t1 : andB (Nat.blt W.t1i nS) (andB (Nat.beq (valF 576 (W.T.tab W.t1i)) (W.reg 86))
    (Nat.beq (clsA (W.aux W.t1i)) 5)) = true
  aux : ∀ c < W.T.C,
    auxRun73 W.R W.T.tab W.aux 576 W.T.wl W.T.wp (c * W.T.B) (cntF nS W.T.B (c * W.T.B)) = true
  aux0 : allN 4 (fun c => Nat.beq (preA (W.aux 0) c) 0) = true
  auxN : allN 4 (fun c => Nat.beq (preA (W.aux nS) c) (getL 0 [7168, 2048, 28672, 759] c)) = true
  z0G : W.Z0G = [W.reg 77, W.reg 78, W.reg 79, W.reg 80]
  z0 : treeOK71 W.Z0G W.Z0P W.Z0Par W.Z0Lab 384 = true
  z0d : distinctL W.Z0P = true
  z0c : canonL W.Z0P = true
  z1G : Z1G = [W.reg 81, W.reg 82]
  z1 : treeOK71 Z1G Z1P Z1Par Z1Lab 1344 = true
  z1d : distinctL Z1P = true
  z1c : canonL Z1P = true
  z2G : Z2G = [W.reg 83, W.reg 84]
  z2 : treeOK71 Z2G Z2P Z2Par Z2Lab 96 = true
  z2d : distinctL Z2P = true
  z2c : canonL Z2P = true
  faith1 : faithK (trK 24 (W.reg 27)) (trK 24 (W.reg 73)) Z1P W.V1 = true
  faith2 : faithK (trK 24 (W.reg 27)) (trK 24 (W.reg 76)) Z2P W.V2 = true

end CFSG.Sporadic.Co1.Module.Odd

end
