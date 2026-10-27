module

public import CFSG.LocalAnalysis.StandardType.GGKGPosSpStd
import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly CFSG.LieType.Universal

section LocalHyp

@[expose] def GGKGPosLocalHypTw (p : ℕ) {G : Type} [Group G] (Bs X : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G) : Prop :=
  (p.Prime ∧ p ≠ 2 ∧ 2 ≤ f ∧ p ∣ 2 ^ f - 1) ∧
    (ψ.ker ≤ Subgroup.center (ggU t n f).K ∧ ψ.range = X) ∧
    (IsElemAbelian p Bs ∧ Bs ≤ Subgroup.normalizer (X : Set G) ∧
      ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) ∧
    (∀ b ∈ Bs, GGPsiInnerDiag (ggU t n f).D ψ b) ∧
    p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ Nat.card ↥Bs ∧
    p ^ 4 ≤ Nat.card ↥Bs

@[expose] def GGKGPosTwInput (t : StatedLieTag) (n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs X : Subgroup G) (f : ℕ)
    (ψ : (ggU t n f).K →* G), GGKGPosLocalHypTw p Bs X t n f ψ → GGTableBPosImage p Bs t n f X

variable {G : Type} [Group G] [Finite G]

theorem ggKGPosLocalHypTw_of_innerDiagOn (hMp : GGInnerDiagMpInput) {p : ℕ}
    {B Bs X : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2) (hBs : GGBstar p B Bs)
    {t : StatedLieTag} {n f : ℕ} (hf : 2 ≤ f) (hpf : p ∣ 2 ^ f - 1) (hrk : 3 ≤ bnRank t n)
    (ψ : (ggU t n f).K →* G) (hadm : StatedLieAdmissible t n 2 f)
    (hker : ψ.ker ≤ Subgroup.center (ggU t n f).K) (hrange : ψ.range = X)
    (hInn : GGInnerDiagOn Bs X)
    (hcard : p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ Nat.card ↥Bs)
    (h4 : p ^ 4 ≤ Nat.card ↥Bs) :
    GGKGPosLocalHypTw p Bs X t n f ψ := by
  have hrk2 : 2 ≤ (ggU t n f).D.rank :=
    two_le_lieUniversal_rank t n 2 f Nat.prime_two hadm hrk
  obtain ⟨-, lab, -, hraw⟩ := hMp G t n f ψ hadm hrk2 hker X hrange _ hInn
  obtain ⟨R, _, I, _, -, -, θ, ⟨hBsN, hI⟩, himp⟩ := largeEvenRawDatum_exists hraw
  exact ⟨⟨hp, hp2, hf, hpf⟩, ⟨hker, hrange⟩, ⟨hBs.2.1, hBsN, hBs.2.2.2⟩,
    fun b hb => himp b (hBsN hb) (hI b hb), hcard, h4⟩

theorem ggKGPosLocalHypTw_of_f4 (hMp : GGInnerDiagMpInput) {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G} (hcfg : GGF4QGeFourCfg p B Bs x L D J y K)
    {t : StatedLieTag} {n f : ℕ} (hf : 2 ≤ f) (hpf : p ∣ 2 ^ f - 1) (hrk : 3 ≤ bnRank t n)
    (ψ : (ggU t n f).K →* G) (hadm : StatedLieAdmissible t n 2 f)
    (hker : ψ.ker ≤ Subgroup.center (ggU t n f).K) (hrange : ψ.range = X)
    (hInn : GGInnerDiagOn Bs X)
    (hcard : p ^ 3 * Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ Nat.card ↥Bs) :
    GGKGPosLocalHypTw p Bs X t n f ψ := by
  obtain ⟨hp, hp2, -, -⟩ := hcfg.1.1.1.2.2.2.2.2.1
  exact ggKGPosLocalHypTw_of_innerDiagOn hMp hp hp2 hcfg.1.1.2.1 hf hpf hrk ψ hadm hker hrange
    hInn hcard hcfg.1.1.tableB_facts.2.2.2.2

theorem ggKGPosLocalHypTw_of_f4_member (hMp : GGInnerDiagMpInput) {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hcfg : GGF4QGeFourCfg p B Bs x L D J y K) (hX : X = L ∨ X = K) {t : StatedLieTag} {n f : ℕ}
    (hf : 2 ≤ f) (hpf : p ∣ 2 ^ f - 1) (hrk : 3 ≤ bnRank t n) (ψ : (ggU t n f).K →* G)
    (hadm : StatedLieAdmissible t n 2 f) (hker : ψ.ker ≤ Subgroup.center (ggU t n f).K)
    (hrange : ψ.range = X) :
    GGKGPosLocalHypTw p Bs X t n f ψ := by
  have hInn : GGInnerDiagOn Bs X := by
    rcases hX with rfl | rfl
    · exact hcfg.1.2.2.1.1
    · exact hcfg.1.2.2.1.2 _ _ hcfg.2.2.2
  exact ggKGPosLocalHypTw_of_f4 hMp hcfg hf hpf hrk ψ hadm hker hrange hInn
    (ggKGPosF4_pow_mul_card_le hcfg hX)

end LocalHyp

section KGPos

theorem ggF4QGeFourKGPosInput_S2_of_inputs (hSU : GGKGPosTwInput .PSU 6)
    (hOm : GGKGPosTwInput .POmegaMinus 4) : GGF4QGeFourKGPosInput .S2 := by
  intro G _ _ p B Bs x L D J y K hcfg _ f hf hpf hrow
  obtain ⟨⟨ψL, hadmL, hkerL, hrangeL⟩, hK⟩ := hrow
  refine ⟨hOm G p Bs L f ψL (ggKGPosLocalHypTw_of_f4_member ggInnerDiagMpInput_holds hcfg
    (Or.inl rfl) hf hpf (by decide) ψL hadmL hkerL hrangeL), ?_⟩
  rcases hK with ⟨ψK, hadmK, hkerK, hrangeK⟩ | ⟨ψK, hadmK, hkerK, hrangeK⟩
  · exact Or.inl (hSU G p Bs K f ψK (ggKGPosLocalHypTw_of_f4_member ggInnerDiagMpInput_holds hcfg
      (Or.inr rfl) hf hpf (by decide) ψK hadmK hkerK hrangeK))
  · exact Or.inr (hOm G p Bs K f ψK (ggKGPosLocalHypTw_of_f4_member ggInnerDiagMpInput_holds hcfg
      (Or.inr rfl) hf hpf (by decide) ψK hadmK hkerK hrangeK))

end KGPos

end CFSG.StandardType
