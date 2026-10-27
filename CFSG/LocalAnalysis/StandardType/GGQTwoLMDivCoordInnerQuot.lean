module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMMod

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary Matrix

theorem qTwoLMDivCoordInner_quot {m : ℕ} (h3 : 3 ∣ m) {X : Type} [Group X]
    (φ : ↥(sumZero m 3) →* X) (hs : Function.Surjective φ)
    (hk : φ.ker = Subgroup.zpowers (qTwoOneVec m h3)) :
    ∃ θ : QTwoHm m h3 ≃* X, ∀ f, θ (QuotientGroup.mk f) = φ f :=
  ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hs), fun _ => rfl⟩

end CFSG.StandardType.QTwo

end
