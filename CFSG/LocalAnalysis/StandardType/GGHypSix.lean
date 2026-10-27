module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceFive

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Abstract

variable {U : Type*} [Group U] (Δ : UniversalRootDatum U) {G : Type*} [Group G]

@[expose] def GGTorusOnRoot (ψ : U →* G) (c : G) (γ : Fin Δ.rank → ℤ) (u : U) : Prop :=
  ∃ g ∈ ψ.range, ∃ h ∈ ggTorus Δ, ∀ z ∈ Δ.rootGroup γ,
    (c * g)⁻¹ * ψ (u * z * u⁻¹) * (c * g) = ψ (u * (h * z * h⁻¹) * u⁻¹)

variable {Δ} in
theorem GGPsiInnerDiag.torusOnRoot {ψ : U →* G} {c : G} (h : GGPsiInnerDiag Δ ψ c)
    {γ : Fin Δ.rank → ℤ} (hγ : γ ∈ Δ.roots) : GGTorusOnRoot Δ ψ c γ 1 := by
  obtain ⟨g, hg, hall⟩ := h
  obtain ⟨t, ht, hz⟩ := hall γ hγ
  exact ⟨g, hg, t, ht, fun z hz' => by simpa using hz z hz'⟩

variable {U' : Type*} [Group U'] (Δ' : UniversalRootDatum U')

@[expose] def GGRootMatch (ψ : U →* G) (ψ' : U' →* G) (δ : Fin Δ'.rank → ℤ)
    (γ : Fin Δ.rank → ℤ) (u : U) : Prop :=
  (∀ z ∈ Δ.rootGroup γ, ∃ z' ∈ Δ'.rootGroup δ, ψ' z' = ψ (u * z * u⁻¹)) ∧
    ∀ h' ∈ ggTorus Δ', ∃ h ∈ ggTorus Δ, ∀ z ∈ Δ.rootGroup γ, ∀ z' ∈ Δ'.rootGroup δ,
      ψ' z' = ψ (u * z * u⁻¹) → ψ' (h' * z' * h'⁻¹) = ψ (u * (h * z * h⁻¹) * u⁻¹)

variable {Δ Δ'} in
theorem ggTorusOnRoot_of_rootMatch {ψ : U →* G} {ψ' : U' →* G} (hle : ψ'.range ≤ ψ.range)
    {δ : Fin Δ'.rank → ℤ} (hδ : δ ∈ Δ'.roots) {γ : Fin Δ.rank → ℤ} {u : U}
    (hm : GGRootMatch Δ Δ' ψ ψ' δ γ u) {c : G} (hc : GGPsiInnerDiag Δ' ψ' c) :
    GGTorusOnRoot Δ ψ c γ u := by
  obtain ⟨g, hg, hall⟩ := hc
  obtain ⟨h', hh', hz'⟩ := hall δ hδ
  obtain ⟨h, hh, hcomp⟩ := hm.2 h' hh'
  refine ⟨g, hle hg, h, hh, fun z hz => ?_⟩
  obtain ⟨z', hz'm, heq⟩ := hm.1 z hz
  rw [← heq, hz' z' hz'm, hcomp z hz z' hz'm heq]

end Abstract

section Inputs

@[expose] def GGCompatPresented {U : Type*} [Group U] {G : Type*} [Group G]
    (Δ : UniversalRootDatum U) (ψ : U →* G) (K : Subgroup G) : Prop :=
  ∃ (t' : StatedLieTag) (n' f' : ℕ) (ψ' : (ggU t' n' f').K →* G),
    StatedLieAdmissible t' n' 2 f' ∧ 2 ≤ (ggU t' n' f').D.rank ∧
    ψ'.ker ≤ Subgroup.center (ggU t' n' f').K ∧ ψ'.range = K ∧
    ∃ δ ∈ (ggU t' n' f').D.roots, ∃ γ ∈ Δ.roots, ∃ u : U,
      GGRootMatch Δ (ggU t' n' f').D ψ ψ' δ γ u

@[expose] def GGRootDetect (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU t n f).K →* G),
    StatedLieAdmissible t n 2 f → 2 ≤ (ggU t n f).D.rank →
    ψ.ker ≤ Subgroup.center (ggU t n f).K →
    ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ (t = .POmegaPlus ∧ n = 4 ∧ p = 3) →
    ∀ c ∈ Subgroup.normalizer (ψ.range : Set G),
      c ^ p ∈ Subgroup.centralizer (ψ.range : Set G) →
      ∀ γ ∈ (ggU t n f).D.roots, ∀ u : (ggU t n f).K, GGTorusOnRoot (ggU t n f).D ψ c γ u →
        GGPsiInnerDiag (ggU t n f).D ψ c

@[expose] def GGCompatNbrInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGOpAutTrivial p Bs → GGInnerDiagAll p B Bs x L D J →
      ∀ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
        GGPresentsG0 (ggG0 p B x L D J) (ggU t n f).D t n f ψ →
          ∃ K : Subgroup G, (K = L ∨ ∃ y : G, GGNbr p B x D J y K) ∧
            GGCompatPresented (ggU t n f).D ψ K

@[expose] def GGHypSixD4Input : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig 3 B Bs x L D J → GGOpAutTrivial 3 Bs → GGInnerDiagAll 3 B Bs x L D J →
      ∀ (f : ℕ) (ψ : (ggU .POmegaPlus 4 f).K →* G),
        GGPresentsG0 (ggG0 3 B x L D J) (ggU .POmegaPlus 4 f).D .POmegaPlus 4 f ψ →
        Bs ≤ Subgroup.normalizer (ggG0 3 B x L D J : Set G) →
          ∀ b ∈ Bs, GGPsiInnerDiag (ggU .POmegaPlus 4 f).D ψ b

end Inputs

section Reduction

variable {G : Type} [Group G] [Finite G]

theorem ggTorusOnRoot_of_innerDiagOn (hR : GGInnerDiagBridgeInput) {U : Type*} [Group U]
    {Δ : UniversalRootDatum U} {ψ : U →* G} {Bs K : Subgroup G} (hK : GGInnerDiagOn Bs K)
    (hcomp : GGCompatPresented Δ ψ K) (hKle : K ≤ ψ.range) :
    ∃ γ ∈ Δ.roots, ∃ u : U, ∀ b ∈ Bs, GGTorusOnRoot Δ ψ b γ u := by
  obtain ⟨t', n', f', ψ', hadm', hrk', hker', hrange', δ, hδ, γ, hγ, u, hm⟩ := hcomp
  obtain ⟨-, lab, -, hraw⟩ := hR G t' n' f' ψ' hadm' hrk' hker' K hrange' _ hK
  obtain ⟨R, _, I, F, -, -, θ, ⟨hBsN, hI⟩, hiff⟩ := largeEvenRawDatum_exists hraw
  refine ⟨γ, hγ, u, fun b hb => ?_⟩
  exact ggTorusOnRoot_of_rootMatch (hrange' ▸ hKle) hδ hm ((hiff b (hBsN hb)).mp (hI b hb))

theorem ggPsiInnerDiag_of_innerDiagOn (hR : GGInnerDiagBridgeInput) {t : StatedLieTag} {n f : ℕ}
    (hdet : GGRootDetect t) {ψ : (ggU t n f).K →* G} (hadm : StatedLieAdmissible t n 2 f)
    (hrk : 2 ≤ (ggU t n f).D.rank) (hker : ψ.ker ≤ Subgroup.center (ggU t n f).K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hD : ¬ (t = .POmegaPlus ∧ n = 4 ∧ p = 3)) {Bs K : Subgroup G}
    (hK : GGInnerDiagOn Bs K) (hcomp : GGCompatPresented (ggU t n f).D ψ K)
    (hKle : K ≤ ψ.range) {b : G} (hb : b ∈ Bs)
    (hbN : b ∈ Subgroup.normalizer (ψ.range : Set G))
    (hbp : b ^ p ∈ Subgroup.centralizer (ψ.range : Set G)) :
    GGPsiInnerDiag (ggU t n f).D ψ b := by
  obtain ⟨γ, hγ, u, hall⟩ := ggTorusOnRoot_of_innerDiagOn hR hK hcomp hKle
  exact hdet G n f ψ hadm hrk hker p hp hp2 hD b hbN hbp γ hγ u (hall b hb)

theorem ggHypSixV2Input_of_detect (hR : GGInnerDiagBridgeInput) (hC : GGCompatNbrInput)
    (hdet : ∀ t, GGRootDetect t) (hD4 : GGHypSixD4Input) : GGHypSixV2Input := by
  intro G _ _ p B Bs x L D J hcfg hOp hInn t n f ψ hpres hBsN b hb
  by_cases hD : t = .POmegaPlus ∧ n = 4 ∧ p = 3
  · obtain ⟨rfl, rfl, rfl⟩ := hD
    exact hD4 G B Bs x L D J hcfg hOp hInn f ψ hpres hBsN b hb
  have hp : p ∈ LargeEvenBeta 4 G := hcfg.1.2.2.2.2.2.1
  obtain ⟨K, hK, hcomp⟩ := hC G p B Bs x L D J hcfg hOp hInn t n f ψ hpres
  have hKinn : GGInnerDiagOn Bs K := by
    rcases hK with rfl | ⟨y, hy⟩
    · exact hInn.1
    · exact hInn.2 y K hy
  have hKle : K ≤ ψ.range := by
    rw [hpres.2.1.1]
    rcases hK with rfl | ⟨y, hy⟩
    · exact le_ggG0_left p B x K D J
    · exact le_ggG0_of_ggNbr hy
  have hbN : b ∈ Subgroup.normalizer (ψ.range : Set G) := by
    rw [hpres.2.1.1]
    exact hBsN hb
  have hbp : b ^ p ∈ Subgroup.centralizer (ψ.range : Set G) := by
    rw [hcfg.2.1.2.1.2 b hb]
    exact Subgroup.one_mem _
  exact ggPsiInnerDiag_of_innerDiagOn hR (hdet t) hpres.1.1 hpres.1.2 hpres.2.1.2 hp.1 hp.2.1 hD
    hKinn hcomp hKle hb hbN hbp

end Reduction

end CFSG.StandardType
