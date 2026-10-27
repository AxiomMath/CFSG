module

public import CFSG.LocalAnalysis.WeakClosure81.TimTI.Nondeg
public import CFSG.LocalAnalysis.WeakClosure81.TimTI.NondegShapes

public section

namespace CFSG.LocalAnalysis.WeakClosure81.TimTI

open CFSG.Quasithin CFSG.Open Subgroup

variable {X : Type} [Group X] [Finite X] {S : Subgroup X}

namespace Hyp

theorem nondeg_shape
    (h : Hyp X S) (hnd : ∃ d ∈ dSet S, ∃ e ∈ dSet S, orderOf (d * e) = 4) :
    SevenElevenASixShape X S ∨ SevenElevenLinearShape X S := by
  have hwc := h.isWC_map_center hnd
  rcases h.psl_or_alt6 hnd with ⟨n, f, hn, hf, hL⟩ | hA
  · exact Or.inr (h.linearShape hwc hn hf hL)
  · exact Or.inl (h.aSixShape hwc hA)

end Hyp

end CFSG.LocalAnalysis.WeakClosure81.TimTI
