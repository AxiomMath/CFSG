module

import all CFSG.Milestones.ASVolI.F4
import all CFSG.Milestones.ASVolI.F4Reductions
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.RankTwoAmalgam CFSG.Quasithin.RankTwoAmalgam.Completion
open CFSG.ASVolI.ChF

theorem burnsideF4n_isQuasiEquivalent_symm {D : Type} [Preorder D] {α : Amalgam.{0, 0} D}
    {G H : Type} [Group G] [Group H] {μ : Amalgam.Completion α G} {η : Amalgam.Completion α H}
    (h : Amalgam.Completion.IsQuasiEquivalent μ η) : Amalgam.Completion.IsQuasiEquivalent η μ := by
  obtain ⟨a, ha⟩ := (Amalgam.Completion.isQuasiEquivalent_iff_exists_act μ η).mp h
  refine (Amalgam.Completion.isQuasiEquivalent_iff_exists_act η μ).mpr ⟨a⁻¹, ?_⟩
  have h1 := Amalgam.Completion.IsEquivalent.act ha a⁻¹
  rw [Amalgam.Completion.act_inv_act] at h1
  exact h1.symm

theorem burnsideF4n_isQuasiEquivalent_trans {D : Type} [Preorder D] {α : Amalgam.{0, 0} D}
    {G H K : Type} [Group G] [Group H] [Group K] {μ : Amalgam.Completion α G}
    {η : Amalgam.Completion α H} {ζ : Amalgam.Completion α K}
    (h₁ : Amalgam.Completion.IsQuasiEquivalent μ η) (h₂ : Amalgam.Completion.IsQuasiEquivalent η ζ) :
    Amalgam.Completion.IsQuasiEquivalent μ ζ := by
  obtain ⟨a, ha⟩ := (Amalgam.Completion.isQuasiEquivalent_iff_exists_act μ η).mp h₁
  obtain ⟨b, hb⟩ := (Amalgam.Completion.isQuasiEquivalent_iff_exists_act η ζ).mp h₂
  refine (Amalgam.Completion.isQuasiEquivalent_iff_exists_act μ ζ).mpr ⟨b * a, ?_⟩
  rw [Amalgam.Completion.act_mul]
  exact (Amalgam.Completion.IsEquivalent.act ha b).trans hb

@[expose] def burnsideF4n_F411RigidExt : Prop :=
  ∀ (κ : GLKind) (p f : ℕ) (E : Type) [Group E] (Gp M₁ M₂ : Subgroup E),
    HypF_4_4 κ p f Gp M₁ M₂ → Gp ≠ ⊤ →
    ∀ ι : Cpl M₁ M₂ ↥(M₁ ⊔ M₂), ι = incl M₁ M₂ →
    ∀ (Y : Type) [Group Y] (μ : Cpl M₁ M₂ Y), μ.IsFaithful → Nonempty (E ≃* μ.G0) →
      Amalgam.Completion.IsQuasiEquivalent μ.toCompletion ι.toCompletion

end CFSG.ASVolI
