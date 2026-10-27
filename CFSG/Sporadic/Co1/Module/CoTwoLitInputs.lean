module

public import CFSG.Sporadic.Co1.Module.CoTwoDataInputs
public import CFSG.Sporadic.Co1.Module.InvFamInputs

@[expose] public section

namespace CFSG.Sporadic.Co1.Module.CoTwo

open CFSG.Sporadic.SmallF2.Native CFSG.KC.InvFam CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT
  CFSG.Sporadic.Co1.Module

def emptyT : STree := ⟨fun _ => 0, 0, 0, 0, 0⟩

structure CoTwoW where
  RA : List ℕ
  RTA : List ℕ
  RS : List ℕ
  RTS : List ℕ
  LV : List (List ℕ)
  SZ : List ℕ
  T : List STree
  TY : STree

noncomputable def commK (R : List ℕ) (c ia ib a b : ℕ) : Bool :=
  Nat.beq (getL 0 R c) (mulF 24 (mulF 24 (mulF 24 (getL 0 R ia) (getL 0 R ib)) (getL 0 R a))
    (getL 0 R b))

structure CoTwoOK (W : CoTwoW) : Prop where
  rA : dat.rowsA = unpackR 24 (getL 0 W.RA 0)
  rB : dat.rowsB = unpackR 24 (getL 0 W.RA 1)
  progA : progK 24 W.RA progA 2 = true
  s0 : getL 0 W.RS 0 = getL 0 W.RA 13
  s1 : getL 0 W.RS 1 = getL 0 W.RA 18
  progS : progK 24 W.RS progS 2 = true
  trA : allN (lenL W.RA) (fun i => Nat.beq (trK 24 (getL 0 W.RA i)) (getL 0 W.RTA i)) = true
  trS : allN (lenL W.RS) (fun i => Nat.beq (trK 24 (getL 0 W.RS i)) (getL 0 W.RTS i)) = true
  fixP : fixAllK W.RTA [9, 10, 14, 15] [2, y₀code] = true
  fixE : fixAllK W.RTA [19, 20] [2] = true
  fixY : fixAllK W.RTA [13, 18] [y₀code] = true
  inv : invPairsK W.RA [9, 10, 14, 15, 19, 20] [11, 12, 16, 17, 21, 22] = true
  comm : andB (commK W.RA 13 11 12 9 10) (andB (commK W.RA 18 16 17 14 15)
    (commK W.RA 23 21 22 19 20)) = true
  lenLV : W.LV.length = baseS.length
  idx : bndK (lenL W.RS) W.LV.flatten = true
  base : bndK (2 ^ 24) baseS = true
  fix : ∀ j < baseS.length, fixAllK W.RTS (W.LV.getD j []) (baseS.take j) = true
  tree : ∀ j < baseS.length, (W.T.getD j emptyT).OK (actV W.RTS (W.LV.getD j []))
    (lenL (W.LV.getD j [])) (baseS.getD j 0) 24 (W.SZ.getD j 0)
  prod : 898128000 ≤ ((List.range baseS.length).map fun j => W.SZ.getD j 0).prod
  ty : W.TY.OK (actV W.RTA [13, 18, 23]) 3 y₀code 24 47104

end CFSG.Sporadic.Co1.Module.CoTwo

end
