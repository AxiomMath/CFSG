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

theorem l2Rows_bpl {k : Nat} {l : List Nat}
    (h : ((Gen.perm (bplArr k)).l2Rows.toList == l) = true) : (bpl k).l2Rows = l.toArray := by
  rw [bpl_eq]
  exact rows_of_toList h

theorem isVis_bpl {k : Nat} (h : (Gen.perm (bplArr k)).isVis = true) : (bpl k).isVis = true := by
  rw [bpl_eq]
  exact h

end CertificateChecks.KernelAP.Baby

end
