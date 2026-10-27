
module

public import CFSG.Sporadic.Co1.Module.TwoBDataInputs
public import Certificates.Data.Kernel.Co1M.TwoBK
public import Certificates.Data.Kernel.TreeK
public import CFSG.Certificates.Kernel.Co1F2Sound

public section

namespace CFSG.Sporadic.Co1.Module.TwoB

open CFSG.KC.Co1M CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.TreeK

structure TwoBW where
  RB : List Nat
  AP : Nat
  N1T : Nat
  N2T : Nat
  SBT : Nat
  P1 : Nat
  P2 : Nat
  PS : Nat
  P1i : Nat
  P2i : Nat
  M01W : List (List Nat)
  M0W : List (List Nat)
  W0 : List Nat
  H : List Nat
  Hi : List Nat
  G : List Nat
  WP : Nat
  WPi : Nat
  TP : Nat
  TX : List (Nat × Nat)
  TPt : List (Nat × Nat)
  TY : List (Nat × Nat)
  TS : List (Nat × Nat)
  TU : List (Nat × Nat)
  YT : List Nat
  ST : List Nat
  EW : List (List Nat × Nat)
  EM : List Nat
  ET : List Nat
  SW : List (List Nat)
  UM : List Nat
  UT : List Nat
  GW : Nat
  Q : Nat
  QI : Nat

@[expose] noncomputable def TwoBW.YR (W : TwoBW) : List Nat := [getL 0 W.RB 8, getL 0 W.RB 12]

@[expose] noncomputable def TwoBW.SR (W : TwoBW) : List Nat :=
  [getL 0 W.RB 33, getL 0 W.RB 34, getL 0 W.RB 35, getL 0 W.RB 36, getL 0 W.RB 37, getL 0 W.RB 38]

@[expose] noncomputable def TwoBW.PN (W : TwoBW) : List Nat := [W.P1, W.P2]

structure TwoBOK (W : TwoBW) : Prop where
  regs : regsRowsB = (W.RB.map (unpackR 24)).toArray
  rbl : W.RB.length = 44
  sb : CFSG.Sporadic.Co1.Module.rowsSB = unpackR 24 (getL 0 W.RB 2)
  tr : andB (trEqK (getL 0 W.RB 3) W.N1T) (andB (trEqK (getL 0 W.RB 4) W.N2T)
    (andB (trEqK (getL 0 W.RB 2) W.SBT) (andB (zipK trEqK W.YR W.YT) (andB (zipK trEqK W.SR W.ST)
      (andB (zipK trEqK W.EM W.ET) (zipK trEqK W.UM W.UT)))))) = true
  e : zipK (ewK [getL 0 W.RB 3, getL 0 W.RB 4]) W.EW W.EM = true
  u : zipK (fun w U => Nat.beq (wK W.SR w) U) W.SW W.UM = true
  perm : andB (permK W.P1 W.P1i) (andB (permK W.P2 W.P2i) (andB (permK W.PS W.PS)
    (andB (permK (getL 0 W.H 0) (getL 0 W.Hi 0)) (andB (permK (getL 0 W.H 1) (getL 0 W.Hi 1))
      (permK W.WP W.WPi))))) = true
  words : andB (zipK (fun w H => Nat.beq (pwK W.PN w) H) W.M01W W.H)
    (andB (zipK (fun w G => Nat.beq (pwK W.PN w) G) W.M0W W.G)
      (andB (Nat.beq (pwK W.PN W.W0) W.WP) (Nat.beq (ppc (ppc W.WP W.PS) W.WPi) W.TP))) = true
  fix : andB (allN 2 fun l => andB (Nat.beq (ppg (getL 0 W.H l) 0) 0)
    (Nat.beq (ppg (getL 0 W.H l) 1) 1))
    (andB (allN 3 fun l => Nat.beq (ppg (getL 0 W.G l) 0) 0) (Nat.beq (ppg W.TP 0) 1)) = true
  gw : andB (Nat.beq (vmF 24 (getL 0 W.YT 0) CFSG.Sporadic.Co1.Module.code4) W.GW)
    (allN 4 fun l => Nat.beq (vmF 24 (getL 0 W.UT l) W.GW) W.GW) = true
  q : andB (Nat.beq (mulF 24 W.Q W.QI) (idF 24)) (Nat.beq (mulF 24 W.QI W.Q) (idF 24)) = true
  sym : symK W.AP = true
  dist : distFK W.AP CFSG.Sporadic.Co1.Module.code4 = true
  ind1 : indK W.AP CFSG.Sporadic.Co1.Module.code4 W.N1T W.P1 = true
  ind2 : indK W.AP CFSG.Sporadic.Co1.Module.code4 W.N2T W.P2 = true
  indS : indK W.AP CFSG.Sporadic.Co1.Module.code4 W.SBT W.PS = true
  indE : ∀ k < 5, ind1K W.AP CFSG.Sporadic.Co1.Module.code4 (getL 0 W.ET k) = true
  econj : distinctK 5 (conjK W.EM (getL 0 W.RB 2)) = true
  einv : invsK W.EM = true
  elen : (prodsK W.EM 5).length = 32
  tx : treeOK (actX W.H W.Hi) 2 11 W.TP W.TX = true
  txl : W.TX.length = 1385
  tp : treeOK (actP W.G) 3 5 1 W.TPt = true
  tpl : W.TPt.length = 22
  ty : treeOK (actV W.YT) 2 12 CFSG.Sporadic.Co1.Module.code4 W.TY = true
  tyl : W.TY.length = 4094
  ts : treeOK (actV W.ST) 6 11 W.GW W.TS = true
  tsl : W.TS.length = 2047
  tu : treeOK (actM W.UM) 4 4 (idF 24) W.TU = true
  tul : W.TU.length = 15
  uni : allN 6 (fun k => uniK (mulF 24 (mulF 24 W.Q (getL 0 W.SR k)) W.QI)) = true
  wd : (∀ k < 2, W.M01W.getD k [] ≠ [] ∧ ∀ l ∈ W.M01W.getD k [], l < 2) ∧
    (∀ k < 3, W.M0W.getD k [] ≠ [] ∧ ∀ l ∈ W.M0W.getD k [], l < 2) ∧
    (W.W0 ≠ [] ∧ ∀ l ∈ W.W0, l < 2) ∧ (∀ k < 5, ∀ l ∈ (W.EW.getD k ([], 0)).1, l < 2) ∧
    ∀ k < 4, ∀ l ∈ W.SW.getD k [], l < 6
  lens : W.EW.length = 5 ∧ W.EM.length = 5 ∧ W.SW.length = 4 ∧ W.M01W.length = 2 ∧
    W.M0W.length = 3

end CFSG.Sporadic.Co1.Module.TwoB

end
