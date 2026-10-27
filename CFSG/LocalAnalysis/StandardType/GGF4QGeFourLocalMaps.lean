module

public import CFSG.LocalAnalysis.StandardType.GGKGPosSpStd

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

theorem ggF4QGeFour_localMap_of_mp
    (hMp : GGInnerDiagMpInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hcfg : GGF4QGeFourCfg p B Bs x L D J y K) (hX : X = L ∨ X = K)
    {t : StatedLieTag} {n f : ℕ} (ψ : (ggU t n f).K →* G)
    (hadm : StatedLieAdmissible t n 2 f) (hrank : 2 ≤ (ggU t n f).D.rank)
    (hker : ψ.ker ≤ Subgroup.center (ggU t n f).K) (hrange : ψ.range = X) :
    Bs ≤ Subgroup.normalizer (X : Set G) ∧
      (∀ b ∈ Bs, GGPsiInnerDiag (ggU t n f).D ψ b) ∧
      p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ Nat.card Bs := by
  have hInn : GGInnerDiagOn Bs X := by
    rcases hX with rfl | rfl
    · exact hcfg.1.2.2.1.1
    · exact hcfg.1.2.2.1.2 _ _ hcfg.2.2.2
  obtain ⟨_, lab, _, hraw⟩ := hMp G t n f ψ hadm hrank hker X hrange _ hInn
  obtain ⟨R, _, I, _, _, _, θ, ⟨hBsN, hI⟩, himp⟩ := largeEvenRawDatum_exists hraw
  exact ⟨hBsN, fun b hb => himp b (hBsN hb) (hI b hb), ggKGPosF4_pow_mul_card_le hcfg hX⟩

end CFSG.StandardType
