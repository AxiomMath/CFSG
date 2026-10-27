module

public import CFSG.Milestones.ASVolI.C31.J4NP.TreeInd
public import Certificates.Certificate7875

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.J4Tree.Native CFSG.J4Tree.Native.Node

section W


theorem burnsideJ4NP_closure2A_Rep {k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ treeN) :
    Subgroup.closure {x | x ∈ burnsideJ4NP_Rep k ∧ burnsideJ4NP_Is2A x} = burnsideJ4NP_Wv k := by
  obtain ⟨hRH, hW⟩ := Certificates.certificate7875 k hk1 hkN
  rw [← hW]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x ⟨hxR, h2A⟩
    by_cases hx1 : x = 1
    · rw [hx1]
      exact Subgroup.one_mem _
    have hsq := burnsideJ4NP_Is2A_sq h2A
    exact Subgroup.subset_closure ⟨hxR, hsq, hx1,
      (burnsideJ4NP_treeT_spec (hRH hxR) hsq hx1).mp h2A⟩
  · rw [Subgroup.closure_le]
    rintro x ⟨hxR, hsq, hx1, ht⟩
    exact Subgroup.subset_closure ⟨hxR, (burnsideJ4NP_treeT_spec (hRH hxR) hsq hx1).mpr ht⟩

end W

end CFSG.ASVolI
