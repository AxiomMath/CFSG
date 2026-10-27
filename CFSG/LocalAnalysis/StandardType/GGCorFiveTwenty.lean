module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOmega
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Defs

variable {G : Type} [Group G] [Finite G]

@[expose] def GGCorFiveTwentyHyp (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G) :
    Prop :=
  GGConfig p B Bs x L D J ∧ GGOpAutTrivial p Bs ∧ GGInnerDiagAll p B Bs x L D J ∧
    GGNoTransvection p Bs ∧ GGInnerDiagOn Bs (ggG0 p B x L D J)

end Defs

@[expose] def GGPseudoReflGenerated {G : Type} [Group G] (p : ℕ) {Bs : Subgroup G}
    (A : Subgroup (MulAut ↥Bs)) : Prop :=
  A = Subgroup.closure {φ | φ ∈ A ∧ GGIsPseudoReflection p φ}

@[expose] def GGPseudoReflOvergroupInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J →
      ∀ φ ∈ ggAutomizer ⊤ Bs, GGIsPseudoReflection p φ → φ ∈ ggAutomizer (ggG0 p B x L D J) Bs

@[expose] def GGWeylPseudoReflGenInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J →
      GGPseudoReflGenerated p (ggAutomizer (ggG0 p B x L D J) Bs)

@[expose] def GGWeylCentralizerScalarInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J →
      ∀ ψ ∈ ggAutomizer ⊤ Bs, (∀ w ∈ ggAutomizer (ggG0 p B x L D J) Bs, ψ * w = w * ψ) →
        GGIsScalar ψ

@[expose] def GGCorFiveTwentyOuterInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J →
      ∀ (g : G) (hg : g ∈ Subgroup.normalizer (Bs : Set G)),
        ggConjAut Bs hg ∈ Subgroup.normalizer
          (ggAutomizer (ggG0 p B x L D J) Bs : Set (MulAut ↥Bs)) →
        (¬ ∃ w ∈ ggAutomizer (ggG0 p B x L D J) Bs, ∀ v ∈ ggAutomizer (ggG0 p B x L D J) Bs,
          ggConjAut Bs hg * v * (ggConjAut Bs hg)⁻¹ = w * v * w⁻¹) →
        g ∈ Subgroup.normalizer (ggG0 p B x L D J : Set G)

@[expose] def GGInnerOnWeylInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J →
      ∀ φ ∈ ggAutomizer ⊤ Bs,
        φ ∈ Subgroup.normalizer (ggAutomizer (ggG0 p B x L D J) Bs : Set (MulAut ↥Bs)) →
        ∃ w ∈ ggAutomizer (ggG0 p B x L D J) Bs, ∀ v ∈ ggAutomizer (ggG0 p B x L D J) Bs,
          φ * v * φ⁻¹ = w * v * w⁻¹

theorem ggCorFiveTwentyOuterInput_of_inner (h : GGInnerOnWeylInput) :
    GGCorFiveTwentyOuterInput := by
  intro G _ _ p B Bs x L D J hH g hg hN hout
  exact absurd (h G p B Bs x L D J hH _
    (ggConjAut_mem_ggAutomizer (Subgroup.mem_top g) hg) hN) hout

@[expose] def GGPseudoReflStabInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J →
      ∀ φ ∈ ggAutomizer (Subgroup.centralizer ({x} : Set G)) Bs, GGIsPseudoReflection p φ →
        φ ∈ ggAutomizer (ggG0 p B x L D J) Bs

@[expose] def GGPseudoReflOrbitInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGCorFiveTwentyHyp p B Bs x L D J →
      ∀ φ ∈ ggAutomizer ⊤ Bs, GGIsPseudoReflection p φ →
        (∀ h ∈ ggG0 p B x L D J, h ∈ Subgroup.normalizer (Bs : Set G) →
          ∀ b : ↥Bs, (b : G) = h * x * h⁻¹ → φ b ≠ b) →
        φ ∈ ggAutomizer (ggG0 p B x L D J) Bs

theorem ggPseudoReflOvergroupInput_of_stab (hRL : GGPseudoReflStabInput)
    (hRO : GGPseudoReflOrbitInput) : GGPseudoReflOvergroupInput := by
  intro G _ _ p B Bs x L D J hH φ hφA hφ
  by_cases hx : ∃ h ∈ ggG0 p B x L D J, h ∈ Subgroup.normalizer (Bs : Set G) ∧
      ∃ b : ↥Bs, (b : G) = h * x * h⁻¹ ∧ φ b = b
  · obtain ⟨h, hhG0, hhN, b, hb, hφb⟩ := hx
    obtain ⟨g, -, hgN, hφg⟩ := mem_ggAutomizer_iff.mp hφA
    have hwW : ggConjAut Bs hhN ∈ ggAutomizer (ggG0 p B x L D J) Bs :=
      ggConjAut_mem_ggAutomizer hhG0 hhN
    have hfix : g * (h * x * h⁻¹) * g⁻¹ = h * x * h⁻¹ := by
      have h1 := congrArg Subtype.val hφb
      rwa [hφg, hb] at h1
    have hgc : h⁻¹ * g * h ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      refine (?_ : x * (h⁻¹ * g * h) = h⁻¹ * g * h * x).symm
      calc x * (h⁻¹ * g * h) = h⁻¹ * ((h * x * h⁻¹) * g) * h := by group
        _ = h⁻¹ * (g * (h * x * h⁻¹) * g⁻¹ * g) * h := by rw [hfix]
        _ = h⁻¹ * g * h * x := by group
    have hgN' : h⁻¹ * g * h ∈ Subgroup.normalizer (Bs : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hhN) hgN) hhN
    have hψ : (ggConjAut Bs hhN)⁻¹ * φ * ggConjAut Bs hhN ∈
        ggAutomizer (Subgroup.centralizer ({x} : Set G)) Bs := by
      rw [mem_ggAutomizer_iff]
      refine ⟨h⁻¹ * g * h, hgc, hgN', fun c => ?_⟩
      rw [MulAut.mul_apply, MulAut.mul_apply, inv_apply_of_forall (ggConjAut_apply Bs hhN), hφg,
        ggConjAut_apply]
      group
    have hψp : GGIsPseudoReflection p ((ggConjAut Bs hhN)⁻¹ * φ * ggConjAut Bs hhN) := by
      have h1 := hφ.conj (ggConjAut Bs hhN)⁻¹
      rwa [inv_inv] at h1
    have hψW := hRL G p B Bs x L D J hH _ hψ hψp
    have heq : φ = ggConjAut Bs hhN * ((ggConjAut Bs hhN)⁻¹ * φ * ggConjAut Bs hhN) *
        (ggConjAut Bs hhN)⁻¹ := by group
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hwW hψW) (Subgroup.inv_mem _ hwW)
  · exact hRO G p B Bs x L D J hH φ hφA hφ
      fun h hhG0 hhN b hb hφb => hx ⟨h, hhG0, hhN, b, hb, hφb⟩

section Proof

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_ggG0_of_scalar {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : LargeEvenSStar p B x L) (hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S)
    (hDJ : LargeEvenStdSubPre p B x L D J) (hBBs : B ≤ Bs) {g h : G}
    (hhG0 : h ∈ ggG0 p B x L D J) (hmem : h⁻¹ * g ∈ Subgroup.normalizer (Bs : Set G))
    (hsc : GGIsScalar (ggConjAut Bs hmem)) :
    g ∈ Subgroup.normalizer (ggG0 p B x L D J : Set G) := by
  have hB : h⁻¹ * g ∈ Subgroup.normalizer (B : Set G) :=
    mem_normalizer_of_ggIsScalar hBBs hmem hsc
  have hX : h⁻¹ * g ∈ Subgroup.normalizer (Subgroup.zpowers x : Set G) :=
    mem_normalizer_of_ggIsScalar (Subgroup.zpowers_le.mpr (hBBs hS.2.1)) hmem hsc
  have hD : h⁻¹ * g ∈ Subgroup.normalizer (D : Set G) :=
    mem_normalizer_of_ggIsScalar (hDJ.1.trans hBBs) hmem hsc
  have hN0 : h⁻¹ * g ∈ Subgroup.normalizer (ggG0 p B x L D J : Set G) :=
    normalizer_inf_le_normalizer_ggG0 hS hnc hDJ ⟨⟨hB, hX⟩, hD⟩
  have := Subgroup.mul_mem _ (Subgroup.le_normalizer hhG0) hN0
  rwa [mul_inv_cancel_left] at this

theorem ggCorFiveTwentyInput_of_reflections (ha₀ : GGLNoncyclicInput)
    (hR : GGPseudoReflOvergroupInput) (hG : GGWeylPseudoReflGenInput)
    (hSc : GGWeylCentralizerScalarInput) (hO : GGCorFiveTwentyOuterInput) :
    GGCorFiveTwentyInput := by
  intro G _ _ p B Bs x L D J hcfg hOp hInn hNoTr hInnG0
  have hH : GGCorFiveTwentyHyp p B Bs x L D J := ⟨hcfg, hOp, hInn, hNoTr, hInnG0⟩
  have hWA : ggAutomizer (ggG0 p B x L D J) Bs ≤ ggAutomizer ⊤ Bs := ggAutomizer_mono Bs le_top
  have hAN := le_normalizer_of_pseudoReflection hWA (hG G p B Bs x L D J hH)
    (hR G p B Bs x L D J hH)
  intro g hg
  have hφA : ggConjAut Bs hg ∈ ggAutomizer ⊤ Bs :=
    ggConjAut_mem_ggAutomizer (Subgroup.mem_top g) hg
  by_cases hinner : ∃ w ∈ ggAutomizer (ggG0 p B x L D J) Bs,
      ∀ v ∈ ggAutomizer (ggG0 p B x L D J) Bs,
        ggConjAut Bs hg * v * (ggConjAut Bs hg)⁻¹ = w * v * w⁻¹
  · obtain ⟨w, hwW, hw⟩ := hinner
    obtain ⟨h, hhG0, hhN, hwh⟩ := mem_ggAutomizer_iff.mp hwW
    have hψA : w⁻¹ * ggConjAut Bs hg ∈ ggAutomizer ⊤ Bs :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (hWA hwW)) hφA
    have hψc : ∀ v ∈ ggAutomizer (ggG0 p B x L D J) Bs,
        w⁻¹ * ggConjAut Bs hg * v = v * (w⁻¹ * ggConjAut Bs hg) := by
      intro v hv
      calc w⁻¹ * ggConjAut Bs hg * v
          = w⁻¹ * (ggConjAut Bs hg * v * (ggConjAut Bs hg)⁻¹) * ggConjAut Bs hg := by group
        _ = w⁻¹ * (w * v * w⁻¹) * ggConjAut Bs hg := by rw [hw v hv]
        _ = v * (w⁻¹ * ggConjAut Bs hg) := by group
    obtain ⟨k, hk⟩ := hSc G p B Bs x L D J hH _ hψA hψc
    have hmem : h⁻¹ * g ∈ Subgroup.normalizer (Bs : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hhN) hg
    have hsc : GGIsScalar (ggConjAut Bs hmem) :=
      ⟨k, fun b => (ggConjAut_inv_mul_apply hg hhN hwh b).trans (hk b)⟩
    exact mem_normalizer_ggG0_of_scalar hcfg.1.2.2.2.2.2.2.1 (ha₀ G p B x L hcfg.1)
      hcfg.2.2.1 hcfg.2.1.1 hhG0 hmem hsc
  · exact hO G p B Bs x L D J hH g hg (hAN hφA) hinner

theorem ggCorFiveTwentyInput_of_stab (ha₀ : GGLNoncyclicInput) (hRL : GGPseudoReflStabInput)
    (hRO : GGPseudoReflOrbitInput) (hG : GGWeylPseudoReflGenInput)
    (hSc : GGWeylCentralizerScalarInput) (hO : GGCorFiveTwentyOuterInput) :
    GGCorFiveTwentyInput :=
  ggCorFiveTwentyInput_of_reflections ha₀ (ggPseudoReflOvergroupInput_of_stab hRL hRO) hG hSc hO

end Proof

theorem ggCorFiveTwentyInputs_of_reflections (ha₀ : GGLNoncyclicInput)
    (hc₃ : GGNoTransvectionInput) (hR : GGPseudoReflOvergroupInput)
    (hG : GGWeylPseudoReflGenInput) (hSc : GGWeylCentralizerScalarInput)
    (hO : GGCorFiveTwentyOuterInput) : GGCorFiveTwentyInput ∧ GGOmegaOneInput :=
  ⟨ggCorFiveTwentyInput_of_reflections ha₀ hR hG hSc hO,
    ggOmegaOneInput_of_noTransvection hc₃⟩

end CFSG.StandardType
