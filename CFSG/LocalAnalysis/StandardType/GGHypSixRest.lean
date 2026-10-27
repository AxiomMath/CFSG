module

public import CFSG.LocalAnalysis.StandardType.GGHypSixRestDetect
public import CFSG.LocalAnalysis.StandardType.GGAssemblyTwoHypSix
public import CFSG.LocalAnalysis.StandardType.GGInnerDiagBridge

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin

section Inputs

@[expose] def GGCompatNbrSomeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      ∀ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
        GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ →
          ∃ (t₀ : StatedLieTag) (n₀ f₀ : ℕ) (ψ₀ : (ggU t₀ n₀ f₀).K →* G),
            GGPresentsG0 (ggG0 p B x L D J) (ggU t₀ n₀ f₀).D t₀ n₀ f₀ ψ₀ ∧
              ∃ K : Subgroup G, (K = L ∨ ∃ y : G, GGNbr p B x D J y K) ∧
                GGCompatPresented (ggU t₀ n₀ f₀).D ψ₀ K

@[expose] def GGHypSixD4SemilinearInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig 3 B Bs x L D J → GGOpAutTrivial 3 Bs → GGInnerDiagAll 3 B Bs x L D J →
      ∀ (f : ℕ) (ψ : (ggU .POmegaPlus 4 f).K →* G),
        GGPresentsG0 (ggG0 3 B x L D J) (ggU .POmegaPlus 4 f).D .POmegaPlus 4 f ψ →
        Bs ≤ Subgroup.normalizer (ggG0 3 B x L D J : Set G) →
          ∀ b ∈ Bs, GGSpinSemilinear (quadPlus 4 (GaloisField 2 f)) ψ b

theorem ggCompatNbrSomeInput_of_compatNbr (hC : GGCompatNbrInput) : GGCompatNbrSomeInput := by
  intro G _ _ p B Bs x L D J hcfg hOp hInn t n f ψ hpres
  obtain ⟨K, hK, hcomp⟩ := hC G p B Bs x L D J hcfg hOp hInn t n f ψ hpres
  exact ⟨t, n, f, ψ, hpres, K, hK, hcomp⟩

end Inputs

section Elements

variable {G : Type} [Group G]

theorem mem_normalizer_range_of_bstar {U : Type*} [Group U] {ψ : U →* G} {G₀ Bs : Subgroup G}
    (hrange : ψ.range = G₀) (hBsN : Bs ≤ Subgroup.normalizer (G₀ : Set G)) {b : G}
    (hb : b ∈ Bs) : b ∈ Subgroup.normalizer (ψ.range : Set G) := by
  rw [hrange]
  exact hBsN hb

theorem pow_mem_centralizer_range_of_bstar [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {U : Type*} [Group U] (ψ : U →* G)
    {b : G} (hb : b ∈ Bs) : b ^ p ∈ Subgroup.centralizer (ψ.range : Set G) := by
  rw [hcfg.2.1.2.1.2 b hb]
  exact Subgroup.one_mem _

end Elements

section Reduction

variable {G : Type} [Group G] [Finite G]

theorem ggPsiInnerDiag_of_presents_two (hMp : GGInnerDiagMpInput) (hMk : GGInnerDiagMarkingInput)
    {G₀ : Subgroup G} {t t₀ : StatedLieTag} {n f n₀ f₀ : ℕ} {ψ : (ggU t n f).K →* G}
    {ψ₀ : (ggU t₀ n₀ f₀).K →* G} (hpres : GGPresentsG0 G₀ (ggU t n f).D t n f ψ)
    (hpres₀ : GGPresentsG0 G₀ (ggU t₀ n₀ f₀).D t₀ n₀ f₀ ψ₀) {c : G}
    (hc : c ∈ Subgroup.normalizer (G₀ : Set G)) (h₀ : GGPsiInnerDiag (ggU t₀ n₀ f₀).D ψ₀ c) :
    GGPsiInnerDiag (ggU t n f).D ψ c := by
  have hm := hMk t₀ G n₀ f₀ ψ₀ G₀ hpres₀
  obtain ⟨⟨hadm, hrk⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
  obtain ⟨-, lab, -, hraw⟩ := hMp G t n f ψ hadm hrk hker G₀ hrange _ hm
  obtain ⟨R, _, I, F, -, -, θ, h1, h2⟩ := largeEvenRawDatum_exists hraw
  exact h2 c hc (h1 c hc h₀)

theorem ggTorusOnRoot_of_compatNbr (hMp : GGInnerDiagMpInput) {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hInn : GGInnerDiagAll p B Bs x L D J) {U : Type*} [Group U]
    {Δ : UniversalRootDatum U} {ψ : U →* G} (hrange : ψ.range = ggG0 p B x L D J)
    {K : Subgroup G} (hK : K = L ∨ ∃ y : G, GGNbr p B x D J y K)
    (hcomp : GGCompatPresented Δ ψ K) :
    ∃ γ ∈ Δ.roots, ∃ u : U, ∀ b ∈ Bs, GGTorusOnRoot Δ ψ b γ u := by
  have hKinn : GGInnerDiagOn Bs K := by
    rcases hK with rfl | ⟨y, hy⟩
    · exact hInn.1
    · exact hInn.2 y K hy
  have hKle : K ≤ ψ.range := by
    rw [hrange]
    rcases hK with rfl | ⟨y, hy⟩
    · exact le_ggG0_left p B x K D J
    · exact le_ggG0_of_ggNbr hy
  exact ggTorusOnRoot_of_innerDiagOn_mp hMp hKinn hcomp hKle

theorem ggHypSixD4Input_of_semilinear (hMp : GGInnerDiagMpInput) (hC : GGCompatNbrInput)
    (hS : GGHypSixD4SemilinearInput) : GGHypSixD4Input := by
  intro G _ _ B Bs x L D J hcfg hOp hInn f ψ hpres hBsN b hb
  obtain ⟨K, hK, hcomp⟩ := hC G 3 B Bs x L D J hcfg hOp hInn .POmegaPlus 4 f ψ hpres
  obtain ⟨γ, hγ, u, hall⟩ := ggTorusOnRoot_of_compatNbr hMp hInn hpres.2.1.1 hK hcomp
  exact ggPsiInnerDiag_D4_of_semilinear hpres.2.1.2 Nat.prime_three (by norm_num)
    (mem_normalizer_range_of_bstar hpres.2.1.1 hBsN hb)
    (pow_mem_centralizer_range_of_bstar hcfg ψ hb) hγ (hall b hb)
    (hS G B Bs x L D J hcfg hOp hInn f ψ hpres hBsN b hb)

theorem ggPsiInnerDiag_of_compatNbr (hMp : GGInnerDiagMpInput) (hdet : ∀ t, GGRootDetect t)
    (hS : GGHypSixD4SemilinearInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hOp : GGOpAutTrivial p Bs)
    (hInn : GGInnerDiagAll p B Bs x L D J) {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* G} (hpres : GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ)
    (hBsN : Bs ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G)) {K : Subgroup G}
    (hK : K = L ∨ ∃ y : G, GGNbr p B x D J y K) (hcomp : GGCompatPresented (ggU t n f).D ψ K)
    {b : G} (hb : b ∈ Bs) : GGPsiInnerDiag (ggU t n f).D ψ b := by
  have hp : p ∈ LargeEvenBeta 4 G := hcfg.1.2.2.2.2.2.1
  obtain ⟨γ, hγ, u, hall⟩ := ggTorusOnRoot_of_compatNbr hMp hInn hpres.2.1.1 hK hcomp
  have hbN := mem_normalizer_range_of_bstar hpres.2.1.1 hBsN hb
  have hbp := pow_mem_centralizer_range_of_bstar hcfg ψ hb
  by_cases hD : t = .POmegaPlus ∧ n = 4 ∧ p = 3
  · obtain ⟨rfl, rfl, rfl⟩ := hD
    exact ggPsiInnerDiag_D4_of_semilinear hpres.2.1.2 hp.1 hp.2.1 hbN hbp hγ (hall b hb)
      (hS G B Bs x L D J hcfg hOp hInn f ψ hpres hBsN b hb)
  · exact hdet t G n f ψ hpres.1.1 hpres.1.2 hpres.2.1.2 p hp.1 hp.2.1 hD b hbN hbp γ hγ u
      (hall b hb)

theorem ggHypSixV2Input_of_someCompat (hMp : GGInnerDiagMpInput)
    (hMk : GGInnerDiagMarkingInput) (h5 : GGCompatNbrSomeInput) (hdet : ∀ t, GGRootDetect t)
    (hS : GGHypSixD4SemilinearInput) : GGHypSixV2Input := by
  intro G _ _ p B Bs x L D J hcfg hOp hInn t n f ψ hpres hBsN b hb
  obtain ⟨t₀, n₀, f₀, ψ₀, hpres₀, K, hK, hcomp⟩ :=
    h5 G p B Bs x L D J hcfg hOp hInn t n f ψ hpres
  exact ggPsiInnerDiag_of_presents_two hMp hMk hpres hpres₀ (hBsN hb)
    (ggPsiInnerDiag_of_compatNbr hMp hdet hS hcfg hOp hInn hpres₀ hBsN hK hcomp hb)

end Reduction

end CFSG.StandardType
