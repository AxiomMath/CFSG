module

public import CFSG.LocalAnalysis.WeakClosure81.TimTI.NondegMain
public import CFSG.LocalAnalysis.WeakClosure81.TimTI.DegenMain

public section

namespace CFSG.LocalAnalysis.WeakClosure81

theorem timmesfeldTIRootInput_holds :
    TimmesfeldTIRootInput := by
  intro X _ _ S hE hc hTI hgen h2 hodd hroot hpair
  have h : TimTI.Hyp X S := ⟨hE, hc, hTI, hgen, h2, hodd, hroot, hpair⟩
  refine ⟨fun s hs t ht hs1 ht1 => h.isConj_of_mem hs ht hs1 ht1, ?_⟩
  by_cases hnd : ∃ d ∈ TimTI.dSet S, ∃ e ∈ TimTI.dSet S, orderOf (d * e) = 4
  · rcases h.nondeg_shape hnd with h6 | hl
    · exact Or.inl h6
    · exact Or.inr (Or.inl hl)
  · have hdeg : ∀ d ∈ TimTI.dSet S, ∀ e ∈ TimTI.dSet S, orderOf (d * e) ≠ 4 :=
      fun d hd e he h4 => hnd ⟨d, hd, e, he, h4⟩
    exact Or.inr (Or.inr (h.degen_shape hdeg))

end CFSG.LocalAnalysis.WeakClosure81
