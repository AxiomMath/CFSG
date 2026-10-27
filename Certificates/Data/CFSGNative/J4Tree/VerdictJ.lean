module

public import Certificates.Data.CFSGNative.J4.F2
public import Certificates.Data.CFSGNative.J4Tree.Aff
public import Certificates.Data.CFSGNative.J4Tree.Index

public section

namespace CFSG.J4Tree.VerdictJ

open CFSG.Sporadic.J4.Native

set_option compiler.extract_closed false

@[inline, expose] def mulT (X T : Array V2) : Array V2 := X.map (frApply T)

@[inline, expose] def letTab (T Ti : Array (Array V2)) (I : Array V2) (l : Int) : Array V2 :=
  if 0 < l then T[l.toNat - 1]?.getD I else Ti[(-l).toNat - 1]?.getD I

@[expose] def wordTab (T Ti : Array (Array V2)) (I : Array V2) (acc : Array V2) (w : List Int) :
    Array V2 :=
  w.foldl (fun acc l => mulT acc (letTab T Ti I l)) acc

@[expose] def w5 (s : String) : List Int :=
  s.toList.filterMap fun ch =>
    if 'a' ≤ ch ∧ ch ≤ 'e' then some ((ch.toNat - 'a'.toNat + 1 : Nat) : Int)
    else if 'A' ≤ ch ∧ ch ≤ 'E' then some (-((ch.toNat - 'A'.toNat + 1 : Nat) : Int))
    else none

structure Ctx where
  lT : Array (Array V2)
  lTi : Array (Array V2)
  cT : Array (Array V2)
  cTi : Array (Array V2)
  idT : Array V2
  uM : Array (Array V2)
  kM : Array (Array V2)
  fM : Array (Array V2)

@[expose] def eltRows (X : Ctx) (fs : List (String × List Int)) : Array V2 :=
  fs.foldl (fun acc f => wordTab X.cT X.cTi X.idT (wordTab X.lT X.lTi X.idT acc (w5 f.1)) f.2)
    idRows

@[expose] def etaRowsV (T : Array (Array V2)) (c : Nat) : Array V2 :=
  (List.range 11).foldl (fun acc j => if c.testBit j then mulRows acc (T[j]?.getD idRows) else acc)
    idRows

@[expose] def kelRowsV (K : Array (Array V2)) (e : Nat) : Array V2 :=
  (CFSG.J4Tree.Native.pcSeqT e).foldl (fun acc i => mulRows acc (K[i]?.getD idRows)) idRows

@[expose] def coordRows (X : Ctx) (p : Nat × Nat) : Array V2 :=
  mulRows (etaRowsV X.uM p.1) (kelRowsV X.kM p.2)

@[expose] def maskRows (Vm : Array (Array V2)) (m : Nat) : Array V2 :=
  (List.range Vm.size).foldl
    (fun acc l => if m.testBit l then mulRows acc (Vm[l]?.getD idRows) else acc) idRows

@[expose] def genRows (X : Ctx) (s : Nat) : Array V2 :=
  if s < 11 then X.uM[s]?.getD idRows else X.kM[s - 11]?.getD idRows

structure NPData where
  node : Nat
  g : List (String × List Int)
  V : List (Nat × Nat)
  masks : List Nat

structure FData where
  node : Nat
  d : List (String × List Int)
  masks : List Nat

@[noinline, expose] def conjOK (X : Ctx) (G : Array V2) (W V : List (Nat × Nat)) : Bool :=
  W.length == V.length && (List.range W.length).all fun i =>
    eqRows (mulRows (coordRows X (W.getD i (0, 0))) G) (mulRows G (coordRows X (V.getD i (0, 0))))

@[noinline, expose] def normOK (X : Ctx) (Vm : Array (Array V2)) (masks : List Nat) : Bool :=
  masks.length == 15 * Vm.size && (List.range 15).all fun s => (List.range Vm.size).all fun i =>
    eqRows (mulRows (genRows X s) (Vm[i]?.getD idRows))
      (mulRows (maskRows Vm (masks.getD (s * Vm.size + i) 0)) (genRows X s))

@[expose] def npOK (X : Ctx) (d : NPData) : Bool :=
  (CFSG.J4Tree.Native.treeWv d.node).all (fun p => decide (p.2 < 1024)) &&
    d.V.all (fun p => decide (p.2 < 1024)) &&
    conjOK X (eltRows X d.g) (CFSG.J4Tree.Native.treeWv d.node) d.V &&
    normOK X (d.V.map (coordRows X)).toArray d.masks

@[noinline, expose] def fConjOK (X : Ctx) (D : Array V2) (Wm : Array (Array V2))
    (masks : List Nat) : Bool :=
  masks.length == 10 && (List.range 10).all fun j =>
    eqRows (mulRows D (X.fM[j]?.getD idRows)) (mulRows (maskRows Wm (masks.getD j 0)) D)

@[expose] def fOK (X : Ctx) (d : FData) : Bool :=
  (CFSG.J4Tree.Native.treeWv d.node).all (fun p => decide (p.2 < 1024)) &&
    fConjOK X (eltRows X d.d) ((CFSG.J4Tree.Native.treeWv d.node).map (coordRows X)).toArray
      d.masks

@[noinline, expose] def npAll (X : Ctx) (ds : List NPData) : Bool := ds.all (npOK X)

@[noinline, expose] def fAll (X : Ctx) (ds : List FData) : Bool := ds.all (fOK X)

end CFSG.J4Tree.VerdictJ
