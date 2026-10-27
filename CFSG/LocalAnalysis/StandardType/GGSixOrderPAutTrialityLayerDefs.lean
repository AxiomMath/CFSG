module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutTrialityDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.StandardType.Triality

@[expose] def GGD4GraphFieldLangInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K), orderOf σ = 3 →
    ∀ γ : Om8 K, (MulAut.conj γ * (theta * AutOm.fieldAutP 4 σ)) ^ 3 = 1 →
      ∃ g : Om8 K, MulAut.conj γ * (theta * AutOm.fieldAutP 4 σ) =
        MulAut.conj g * (theta * AutOm.fieldAutP 4 σ) * (MulAut.conj g)⁻¹

@[expose] def GGD4GraphFieldFixQuasisimpleInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (σ : K ≃+* K), orderOf σ = 3 →
    CFSG.Assembly.IsQuasisimple ↥(ggFix (theta * AutOm.fieldAutP 4 σ))

@[expose] def GGD4GraphClassInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (f : ℕ), Nat.card K = 2 ^ f → 3 ∣ 2 ^ f - 1 →
    ∀ γ : Om8 K, (MulAut.conj γ * theta) ^ 3 = 1 →
      (∃ g : Om8 K, MulAut.conj γ * theta = MulAut.conj g * theta * (MulAut.conj g)⁻¹) ∨
        LieModel (↥(LargeEvenLayer (ggFix (MulAut.conj γ * theta))) ⧸
          Subgroup.center ↥(LargeEvenLayer (ggFix (MulAut.conj γ * theta)))) .PSL 3 2 f

@[expose] def GGD4GraphFixQuasisimpleInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 3 ∣ Nat.card K - 1 →
    CFSG.Assembly.IsQuasisimple ↥(ggFix (theta : MulAut (Om8 K)))

end CFSG.StandardType
