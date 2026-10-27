module

public import Certificates.Data.Kernel.J4TreeNode
public import Certificates.Data.CFSGNative.J4Tree.Tree

public section

namespace CFSG.KC.J4TreeN

open CFSG.J4Tree.Native CFSG.J4Tree.Native.Node

@[expose] noncomputable def chunkNodeOK (T : Tabs) (c : Nat) (R : Nat → NRec) (j : Nat) : Bool :=
  100 * c + j == 0 || Nat.blt treeN (100 * c + j) || treeTopIds.contains (100 * c + j) ||
    nodeChk T (100 * c + j) (R j)

@[expose] noncomputable def edgeChk (c : Nat) (R : Nat → NRec) : Bool :=
  (List.range' 1 treeN).all fun k =>
    !((treeParent k).1 / 100 == c) || (treeParent k).1 == 0 ||
      (Nat.ble (treeParent k).1 treeN && !(treeTopIds.contains (treeParent k).1) &&
        ((R ((treeParent k).1 % 100)).kids.getD (treeParent k).2 default).tgt == k)

@[expose] noncomputable def wAllOK (T : Tabs) (R : Nat → WRec) (k : Nat) : Bool :=
  k == 0 || Nat.blt treeN k || wChk T k (R k)

end CFSG.KC.J4TreeN

end
