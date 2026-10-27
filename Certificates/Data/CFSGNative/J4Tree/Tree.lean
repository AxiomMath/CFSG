module

public import Certificates.Data.CFSGNative.J4Tree.Node
public import Certificates.Data.CFSGNative.J4Tree.TreeData

public section

namespace CFSG.J4Tree.Native.Node

open CFSG.J4Tree.Native

set_option compiler.extract_closed false

@[expose] def chunkStr (c : Nat) : String :=
  match c with
  | 0 => chunk00 | 1 => chunk01 | 2 => chunk02 | 3 => chunk03 | 4 => chunk04 | 5 => chunk05
  | 6 => chunk06 | 7 => chunk07 | 8 => chunk08 | 9 => chunk09 | 10 => chunk10 | 11 => chunk11
  | 12 => chunk12 | 13 => chunk13 | _ => ""

@[expose] def chunkNodes (c : Nat) : List NodeData := parseChunk (chunkStr c)

@[expose] def nodeData (k : Nat) : NodeData :=
  ((chunkNodes (k / 100)).find? (fun nd => nd.id == k)).getD default

@[expose] def treeParent (k : Nat) : Nat × Nat := treeParentTab[k]?.getD (0, 0)

@[expose] def kidTgtIn (nodes : List NodeData) (k₀ j : Nat) : Nat :=
  match nodes.find? (fun nd => nd.id == k₀) with
  | some nd => (nd.kids[j]?.map Kid.tgt).getD 0
  | none => 0

@[expose] def globalOK : Bool :=
  treeBasis 1 == [(1131, 0)] &&
    (List.range' 1 treeN).all fun k => treeTopIds.contains k || treeTopKids.contains k ||
      (decide (1 ≤ (treeParent k).1) && decide ((treeParent k).1 < k) &&
        !(treeTopIds.contains (treeParent k).1))

@[noinline, expose] def chunkOKWith (t : Code → Bool) (c : Nat) (nodes : List NodeData) : Bool :=
  (List.range' (100 * c) 100).all (fun k => k == 0 || decide (treeN < k) || treeTopIds.contains k ||
      match nodes.find? (fun nd => nd.id == k) with
      | some nd => nodeOK t nd
      | none => false) &&
    (List.range' 1 treeN).all (fun k => !((treeParent k).1 / 100 == c) ||
      (treeParent k).1 == 0 || kidTgtIn nodes (treeParent k).1 (treeParent k).2 == k) &&
    globalOK

@[expose] def chunkOK (t : Code → Bool) (c : Nat) : Bool := chunkOKWith t c (chunkNodes c)

@[noinline, expose] def wvOKWith (t : Code → Bool) (bc wc : List Code) (A W : Std.HashSet Code) :
    Bool :=
  A.contains 1 && closedUnder bc rmul A && W.contains 1 && closedUnder wc rmul W &&
    wc.all (fun w => A.contains w && w * w == 1 && w != 1 && t w) &&
    A.toList.all (fun a => a == 1 || !(t a) || W.contains a)

@[expose] def wvOK (t : Code → Bool) (k : Nat) : Bool :=
  (treeBasis k).all (fun ce => decide (ce.2 < 1024)) &&
    (treeWv k).all (fun ce => decide (ce.2 < 1024)) &&
    wvOKWith t ((treeBasis k).map cc) ((treeWv k).map cc)
      (bfsFrom ((treeBasis k).map cc) rmul 1 4096) (bfsFrom ((treeWv k).map cc) rmul 1 4096)

@[expose] def wvAllOK (t : Code → Bool) : Bool := (List.range' 1 treeN).all (wvOK t)

end CFSG.J4Tree.Native.Node
