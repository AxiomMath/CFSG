module

public import CFSG.LocalAnalysis.StandardType.ExcPos.UnitDefs
public import CFSG.LocalAnalysis.StandardType.GGFinModelRootCompatDefs
public import CFSG.LocalAnalysis.StandardType.GGLieBridgeHom
public import CFSG.LocalAnalysis.StandardType.GGLieBridgeTheta
public import CFSG.LocalAnalysis.StandardType.GGLieBridgePartner
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart8

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.Blueprint.Chevalley
  CFSG.StandardType.ClassicalPosition CFSG.StandardType.GGFinModel CFSG.StandardType.LieCore

theorem excU1a_bridge_of
    {t : StatedLieTag} (ht : GGExcFive t) {X : Type} [Group X] [Finite X]
    {n f : ℕ} {ψ : (ggU t n f).K →* X} {G₀ B₁ : Subgroup X}
    (hpres : GGPresentsG0 G₀ (ggU t n f).D t n f ψ)
    (h7 : B₁ ≤ Subgroup.normalizer (G₀ : Set X))
    (h8 : ∀ b ∈ B₁, GGPsiInnerDiag (ggU t n f).D ψ b) :
    ∃ (hf : 1 ≤ f) (θ : ↥G₀ →* ModGL (langTag t) GGL) (lam : ↥B₁ →* ModGL (langTag t) GGL),
      θ.ker = Subgroup.center ↥G₀ ∧ θ.range = ⁅ggFixGp t f, ggFixGp t f⁆ ∧
      (∀ (k : (ggU t n f).K) (hk : ψ k ∈ G₀), θ ⟨ψ k, hk⟩ = ggIotaK t n f hf k) ∧
      (∀ z ∈ ggFixGp t f, (∀ y, z * θ y = θ y * z) → z = 1) ∧
      (∀ b, lam b ∈ ggFixGp t f) ∧ (∀ b : ↥B₁, GGLiePartner G₀ θ b (lam b)) ∧
      ∀ b : ↥B₁, lam b = 1 ↔ (b : X) ∈ Subgroup.centralizer (G₀ : Set X) := by
  have hf : 1 ≤ f := hpres.1.1.2.1
  have ht5 : GGExcFive t := ht
  have hperf : commutator ↥G₀ = ⊤ := hpres.2.2.1
  obtain ⟨θ, hθc, hθker, hθrange, hθcent⟩ := ggLieBridge_theta ht5 hf hpres
  have hΓ : θ.range ≤ ggFixGp t f := by
    rw [hθrange]
    refine Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => ?_
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h₁ h₂)
      (Subgroup.inv_mem _ h₁)) (Subgroup.inv_mem _ h₂)
  have hpart : ∀ d ∈ B₁, ∃ a ∈ ggFixGp t f, GGLiePartner G₀ θ d a :=
    fun d hd => ggLiePartner_exists ht5 hf hpres hΓ hθc (h7 hd) (h8 d hd)
  obtain ⟨lam, hlam⟩ :=
    CFSG.StandardType.F4ExplicitPos.Partner.exists_partner_hom
      (G := X) (Y := ModGL (langTag t) GGL) (G₀ := G₀) (D := B₁)
      (Φ := ggFixGp t f) (θ := θ) hθcent h7 hpart
  refine ⟨hf, θ, lam, hθker, hθrange, hθc, hθcent, fun b => (hlam b).1,
    fun b => (hlam b).2, ?_⟩
  intro b
  constructor
  · intro hb1
    have htriv : ∀ x : ↥G₀, ∀ hx : (b : X) * (x : X) * (b : X)⁻¹ ∈ G₀,
        θ ⟨_, hx⟩ = θ x := by
      intro x hx
      have hh := (hlam b).2 x hx
      rw [hb1] at hh
      simpa using hh
    exact centralizes_of_trivial_bridge_action θ hperf hθker (h7 b.2) htriv
  · intro hbC
    have h1part : GGLiePartner G₀ θ (b : X) 1 := by
      intro x hx
      have hdx : (b : X) * (x : X) * (b : X)⁻¹ = (x : X) :=
        mul_inv_eq_iff_eq_mul.mpr
          (Subgroup.mem_centralizer_iff.mp hbC (x : X) x.2).symm
      simp only [one_mul, inv_one, mul_one]
      exact congrArg θ (Subtype.ext hdx)
    exact GGLiePartner.unique hθcent (h7 b.2) (hlam b).1 (Subgroup.one_mem _)
      (hlam b).2 h1part

theorem excU1a_bridge
    {t : StatedLieTag} (ht : GGExcFive t) {X : Type} [Group X] [Finite X]
    {n f p : ℕ} {ψ : (ggU t n f).K →* X} {G₀ B₁ D J L : Subgroup X} {x : X}
    (h : GGSixPosHyp t n f ψ p G₀ B₁ D J L x) :
    ∃ (hf : 1 ≤ f) (θ : ↥G₀ →* ModGL (langTag t) GGL) (lam : ↥B₁ →* ModGL (langTag t) GGL),
      θ.ker = Subgroup.center ↥G₀ ∧ θ.range = ⁅ggFixGp t f, ggFixGp t f⁆ ∧
      (∀ (k : (ggU t n f).K) (hk : ψ k ∈ G₀), θ ⟨ψ k, hk⟩ = ggIotaK t n f hf k) ∧
      (∀ z ∈ ggFixGp t f, (∀ y, z * θ y = θ y * z) → z = 1) ∧
      (∀ b, lam b ∈ ggFixGp t f) ∧ (∀ b : ↥B₁, GGLiePartner G₀ θ b (lam b)) ∧
      ∀ b : ↥B₁, lam b = 1 ↔ (b : X) ∈ Subgroup.centralizer (G₀ : Set X) := by
  obtain ⟨h1, h2, h3, -, -, -, h7, h8, -⟩ := h
  have hadm : StatedLieAdmissible t n 2 f := CFSG.Blueprint.LieModel.admissible h3
  have hrk : 2 ≤ (ggU t n f).D.rank := by
    rcases ht with hF4 | hE6 | hE7 | hE8 | hTwE6
    · subst hF4
      rw [ggRank_untw (Or.inl rfl) n f]
      decide
    · subst hE6
      rw [ggRank_untw (Or.inr (Or.inl rfl)) n f]
      decide
    · subst hE7
      rw [ggRank_untw (Or.inr (Or.inr (Or.inl rfl))) n f]
      decide
    · subst hE8
      rw [ggRank_untw (Or.inr (Or.inr (Or.inr rfl))) n f]
      decide
    · subst hTwE6
      rw [show (ggU .twistedE6 n f).D.rank = 4 from rfl]
      decide
  have hperfU : commutator (ggU t n f).K = ⊤ := (ggU_perfect_lieModel hadm hrk).1
  have hperf : commutator ↥G₀ = ⊤ := by
    rw [← h1]
    have hsurj : Function.Surjective (MonoidHom.rangeRestrict ψ) :=
      MonoidHom.rangeRestrict_surjective ψ
    have hmap : Subgroup.map (MonoidHom.rangeRestrict ψ) (commutator (ggU t n f).K) =
        commutator ↥ψ.range := by
      rw [commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ hsurj, commutator_def]
    rw [hperfU, Subgroup.map_top_of_surjective _ hsurj] at hmap
    exact hmap.symm
  have hpres : GGPresentsG0 G₀ (ggU t n f).D t n f ψ :=
    ⟨⟨hadm, hrk⟩, ⟨h1, h2⟩, hperf, h3⟩
  exact excU1a_bridge_of ht hpres h7 h8

end CFSG.StandardType.LieKnownR2.ExcPos
