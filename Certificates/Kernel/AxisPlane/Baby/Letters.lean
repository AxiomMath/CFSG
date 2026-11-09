module

public import CFSG.Monster.AxisCount.BabyBasic
public import Certificates.Kernel.AxisPlane.Letters

public section

namespace CertificateChecks.KernelAP.Baby

open CFSG.Monster.AxisCount.Native CFSG.Monster.AxisCount.Baby CertificateChecks.KernelAP

@[expose] def bplArr (k : Nat) : Array Nat :=
  if k < 200 then
    if k < 100 then babyPermChunk0[k]! else babyPermChunk1[k - 100]!
  else babyPermChunk2[k - 200]!

theorem bpl_eq (k : Nat) : bpl k = .perm (bplArr k) := by
  have s0 : babyPermChunk0.size = 100 := rfl
  have s1 : babyPermChunk1.size = 100 := rfl
  simp only [bpl, babyPermTab, bplArr, getElem!_append_ite, Array.size_append, s0, s1,
    Nat.reduceAdd]

theorem l2Rows_bpl {k : Nat} {l : List Nat} (hv : (bpl k).isVis = true)
    (h : ((fastRowsPB (bplArr k)).toList == l) = true) : (bpl k).l2Rows = l.toArray := by
  rw [bpl_eq] at hv ⊢
  rw [FastRowsL.l2Rows_perm hv, ← PopcBL.fastRowsPB_eq]
  exact rows_of_toList h

theorem isVis_bpl {k : Nat} (h : permValidF (bplArr k) = true) : (bpl k).isVis = true := by
  rw [bpl_eq]
  exact ParFoldL.isVis_perm h

end CertificateChecks.KernelAP.Baby

end
