module

public import Certificates.Data.Kernel.J4TreeNode
public import Certificates.Data.CFSGNative.J4Tree.Tree

public section

namespace CFSG.KC.J4TreeN

open CFSG.J4Tree.Native CFSG.J4Tree.Native.Node

@[expose] noncomputable def chunkNodeOK (T : Tabs) (c : Nat) (R : Nat → NRec) (j : Nat) : Bool :=
  100 * c + j == 0 || Nat.blt treeN (100 * c + j) || treeTopIds.contains (100 * c + j) ||
    nodeChk T (100 * c + j) (R j)

@[expose] noncomputable def nodeFlds (F : Nat → Nat) (o : Nat) : List Nat :=
  (List.range' (o % 1048576) (o / 1048576)).flatMap fun i => decF 1048576 (F i)

@[expose] noncomputable def edgeChk (c : Nat) (R : Nat → NRec) : Bool :=
  treeParentTab.toList.zipIdx.all fun e =>
    !(e.1.1 / 100 == c) || e.1.1 == 0 ||
      (Nat.ble e.1.1 treeN && !(treeTopIds.contains e.1.1) &&
        ((R (e.1.1 % 100)).kids.getD e.1.2 default).tgt == e.2)

@[expose] noncomputable def edgeNodeChk (c : Nat) (R : Nat → NRec) (j : Nat) : Bool :=
  treeParentTab.toList.zipIdx.all fun e =>
    !(e.1.1 == 100 * c + j) || e.1.1 == 0 ||
      (Nat.ble e.1.1 treeN && !(treeTopIds.contains e.1.1) &&
        ((R j).kids.getD e.1.2 default).tgt == e.2)

theorem edgeChk_of_nodes {c : Nat} {R : Nat → NRec} (h : ∀ j < 100, edgeNodeChk c R j = true) :
    edgeChk c R = true := by
  unfold edgeChk
  refine List.all_eq_true.mpr fun e he => ?_
  by_cases hc : e.1.1 / 100 = c
  · have hj := List.all_eq_true.mp (h (e.1.1 % 100) (Nat.mod_lt _ (by decide))) e he
    have hp : e.1.1 = 100 * c + e.1.1 % 100 := by omega
    rw [← hp] at hj
    simpa [hc] using hj
  · simp [hc]

@[expose] noncomputable def wAllOK (T : Tabs) (R : Nat → WRec) (k : Nat) : Bool :=
  k == 0 || Nat.blt treeN k || wChk T k (R k)

end CFSG.KC.J4TreeN

end
