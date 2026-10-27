module

public import CFSG.LocalAnalysis.WeakClosure81.TimTI.DegenConn
public import CFSG.LocalAnalysis.WeakClosure81.TimTI.DegenConnGen
public import CFSG.LocalAnalysis.WeakClosure81.TimTI.BenderShape
public import CFSG.LocalAnalysis.WeakClosure81.TimTI.BenderGen

public section

namespace CFSG.LocalAnalysis.WeakClosure81.TimTI

open CFSG.Quasithin CFSG.Open Subgroup

variable {X : Type} [Group X] [Finite X] {S : Subgroup X}

namespace Hyp

theorem degen_shape
    (h : Hyp X S) (hdeg : ∀ d ∈ dSet S, ∀ e ∈ dSet S, orderOf (d * e) ≠ 4) : RootShape X S := by
  obtain ⟨s, hs, -, -, hs1, -, -⟩ := h.exists_ne_ne_one
  have hsD : s ∈ dSet S := mem_dSet_of_mem hs hs1
  by_cases hdisc : CFSG.Timmesfeld.Connectivity.Disconnected
      (QuotientGroup.mk' (Subgroup.center X) '' dSet S)
  · obtain ⟨n, hn, hcard, hshape, hsub⟩ := h.bender_shape hdeg hdisc hs hs1
    obtain ⟨g, hg⟩ := h.bender_gen hdeg hdisc hs hs1 hcard
    exact ⟨n, by omega, _, h.le_rootGroup hdeg hs hs1, h.isElemAbelian_rootGroup hsD, hcard,
      ⟨g, hg⟩, hshape, h.isOddTransp_conj_rootGroup hdeg hsub⟩
  · obtain ⟨f, hf, hcard, hshape⟩ := h.conn_rootGroupShape hdeg hdisc hs hs1
    obtain ⟨g, hg⟩ := h.conn_gen hdeg hdisc hs hs1 hcard
    exact ⟨f, by omega, _, h.le_rootGroup hdeg hs hs1, h.isElemAbelian_rootGroup hsD, hcard,
      ⟨g, hg⟩, hshape, h.isOddTransp_conj_rootGroup hdeg (h.conn_rootGroup_sub hdeg hdisc hsD)⟩

end Hyp

end CFSG.LocalAnalysis.WeakClosure81.TimTI
