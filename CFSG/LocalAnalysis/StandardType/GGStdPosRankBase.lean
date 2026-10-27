module

public import CFSG.LocalAnalysis.StandardType.GGStdPosRankDefs
public import CFSG.LocalAnalysis.StandardType.GGStdPosRankCard
public import CFSG.LocalAnalysis.StandardType.GGStdPosRankThree
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdAssembly
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionRank

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal

theorem ggKGPos_innerDiagOn {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} (h : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {X : Subgroup G} (hX : X = L ∨ X ∈ 𝒦) : GGInnerDiagOn Bs X := by
  have hInn : GGInnerDiagAll p B Bs x L D J := h.1.2.2.1
  rcases hX with rfl | hXK
  · exact hInn.1
  · obtain ⟨y, hy⟩ := h.2.2.2.1.2 X hXK
    exact hInn.2 y X hy

theorem ggKGPosBaseStmt_holds :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
      (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
        ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → GGSplitLie p X →
          ∃ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
            GGKGPosBaseHyp p Bs X t n f ψ := by
  intro G _ _ p B Bs x L D J 𝒦 h X hX hsplit
  obtain ⟨t, n, f, ψ, hadm, hker, hrange, ht, hpf⟩ := hsplit
  obtain ⟨hp, hp2, h4⟩ := ggKGPos_prime_rank_ge_four h
  have hInn := ggKGPos_innerDiagOn h hX
  have hBsG : GGBstar p B Bs := h.1.1.2.1
  have hcard : p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ Nat.card ↥Bs :=
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hp.pos (by omega))).trans
      (ggKGPos_pow_mul_card_le h hX)
  have hrk : 3 ≤ bnRank t n :=
    ggKGPos_three_le_bnRank ggLabelRigidInput_holds hp hadm hker hrange ht hpf hBsG.2.1 hInn hcard
  have hrk2 : 2 ≤ (ggU t n f).D.rank := two_le_lieUniversal_rank t n 2 f Nat.prime_two hadm hrk
  obtain ⟨-, lab, -, hraw⟩ := ggInnerDiagMpInput_holds G t n f ψ hadm hrk2 hker X hrange _ hInn
  obtain ⟨R, _, I, _, -, -, θ, ⟨hBsN, hI⟩, himp⟩ := largeEvenRawDatum_exists hraw
  exact ⟨t, n, f, ψ, ⟨hp, hp2, hadm, hrk⟩, ⟨hker, hrange, ht, hpf⟩,
    ⟨hBsG.2.1, hBsN, hBsG.2.2.2⟩, fun b hb => himp b (hBsN hb) (hI b hb)⟩

end CFSG.StandardType

end
