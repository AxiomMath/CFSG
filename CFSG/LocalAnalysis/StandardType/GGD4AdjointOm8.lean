module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityBridge

public section

namespace CFSG.StandardType.TriBridge

open CFSG.Blueprint.Chevalley CFSG.StandardType.Triality

theorem d4_adjoint_equiv_om8
    {K : Type} [Field K] [Finite K] [CharP K 2] :
    ∃ Φ : adjointGroup .D4 K ≃* Om8 K, ∀ β ∈ rootFinset .D4, ∀ c : K,
      Φ ⟨pinnedX .D4 K β c, pinnedX_mem_adjointGroup β c⟩ = X8 (bLinv β) c := by
  refine ⟨bridge.symm, fun β hβ c => (MulEquiv.symm_apply_eq bridge).2 (Subtype.ext ?_)⟩
  have h := coe_bridge_X8 (K := K) (bLinv_mem (mem_rootFinset.1 hβ)) c
  exact (h.trans (congrArg (fun w => pinnedX TwistTag.D4.tag K w c) (bL_bLinv β))).symm

end CFSG.StandardType.TriBridge

end
