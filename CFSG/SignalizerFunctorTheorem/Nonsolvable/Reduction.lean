module

public import CFSG.SignalizerFunctorTheorem.Assembly
public import CFSG.SignalizerFunctorTheorem.Inheritance

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem

@[expose] def McBrideCompletenessAt (p : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), IsElemAbelian p A →
    p ^ 3 ≤ Nat.card A → ∀ Θ : Subgroup G → Subgroup G, IsSignalizerFunctor p 1 A Θ →
    (∀ S ∈ signalizerFunctorEk p 1 A, signalizerMcBrideHypothesisB p (Θ S)) →
    IsComplete p 1 A Θ

@[expose] def FaithfulSectionExclusionAt (p : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), IsElemAbelian p A →
    p ^ 3 ≤ Nat.card A → ∀ Θ : Subgroup G → Subgroup G, IsSignalizerFunctor p 1 A Θ →
    (∀ S ∈ signalizerFunctorEk p 1 A, signalizerMcBrideHypothesisB p (Θ S)) →
    IsComplete p 1 A Θ → NoFaithfulSection A (completion p 1 A Θ)

theorem mcBrideRankOneTheoremAt_of (p : ℕ) (hp : p.Prime) (hcomplete : McBrideCompletenessAt p)
    (hexclusion : FaithfulSectionExclusionAt p) : McBrideRankOneTheoremAt p := by
  intro G _ _ A hA hlarge Θ hΘ hK
  have hW := hcomplete G A hA hlarge Θ hΘ hK
  refine ⟨hW, mcBrideHypothesisB_of_centralizers hp hA (le_normalizer_completion hΘ.normalized)
    hW.1 (fun a ha ha1 => ?_) (hexclusion G A hA hlarge Θ hΘ hK hW)⟩
  have hz := zpowers_mem_E1 hp hA ha ha1
  rw [← centralizer_zpowers, hW.2 _ hz]
  exact hK _ hz

end CFSG.SignalizerFunctorTheorem
