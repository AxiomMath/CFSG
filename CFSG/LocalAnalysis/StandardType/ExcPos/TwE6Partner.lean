module

public import CFSG.LocalAnalysis.StandardType.GGLieBridgeHolds

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.LieCore CFSG.LieType.Universal CFSG.Blueprint CFSG.Blueprint.Chevalley


private theorem lk0xttpart_exists_lam {G Y : Type} [Group G] [Group Y] {G₀ D : Subgroup G}
    {Φ : Subgroup Y} {θ : ↥G₀ →* Y}
    (hcent : ∀ z ∈ Φ, (∀ x : ↥G₀, z * θ x = θ x * z) → z = 1)
    (hDN : D ≤ Subgroup.normalizer (G₀ : Set G))
    (hpart : ∀ d ∈ D, ∃ a ∈ Φ, GGLiePartner G₀ θ d a) :
    ∃ lam : ↥D →* Y, ∀ d : ↥D, lam d ∈ Φ ∧ GGLiePartner G₀ θ (d : G) (lam d) := by
  classical
  choose f hfΦ hfp using fun d : ↥D => hpart d d.2
  have hmul : ∀ d d' : ↥D, f (d * d') = f d * f d' := by
    intro d d'
    refine GGLiePartner.unique hcent (hDN (d * d').2) (hfΦ (d * d'))
      (mul_mem (hfΦ d) (hfΦ d')) ?_ ?_
    · exact hfp (d * d')
    · rw [Subgroup.coe_mul]
      exact GGLiePartner.mul (hDN d.2) (hDN d'.2) (hfp d) (hfp d')
  exact ⟨MonoidHom.mk' f hmul, fun d => ⟨hfΦ d, hfp d⟩⟩

theorem exists_twE6_partner {X : Type} [Group X] [Finite X] {n f p : ℕ} (hf : 1 ≤ f)
    {ψ : (ggU .twistedE6 n f).K →* X} {G₀ A : Subgroup X} (hp : p.Prime) (hp2 : p ≠ 2)
    (hHyp : GGLieBridgeHyp .twistedE6 n f p ψ G₀ A) :
    ∃ (θ : ↥G₀ →* ModGL (langTag .twistedE6) GGL) (Θ : ↥A →* ModGL (langTag .twistedE6) GGL),
      (∀ (k : (ggU .twistedE6 n f).K) (h : ψ k ∈ G₀),
        θ ⟨ψ k, h⟩ = ggIotaK .twistedE6 n f hf k) ∧
      θ.ker = Subgroup.center ↥G₀ ∧ θ.range = ⁅ggFixGp .twistedE6 f, ggFixGp .twistedE6 f⁆ ∧
      (∀ a : ↥A, Θ a ∈ ggFixGp .twistedE6 f) ∧
      (∀ a : ↥A, Θ a = 1 ↔ (a : X) ∈ Subgroup.centralizer (G₀ : Set X)) ∧
      (∀ a : ↥A, GGLiePartner G₀ θ (a : X) (Θ a)) := by
  have ht : GGExcFive .twistedE6 := Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  have hpres := ggPresentsG0_of_bridgeHyp ht hHyp
  obtain ⟨θ, hθc, hθker, hθrange, hθcent⟩ := ggLieBridge_theta ht hf hpres
  have hΓ : θ.range ≤ ggFixGp .twistedE6 f := by
    rw [hθrange]
    refine Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => ?_
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h₁ h₂)
      (Subgroup.inv_mem _ h₁)) (Subgroup.inv_mem _ h₂)
  obtain ⟨-, -, -, hDN, hDinn, -, -⟩ := hHyp
  obtain ⟨Θ, hΘ⟩ := lk0xttpart_exists_lam (G₀ := G₀) (D := A)
    (Φ := ggFixGp .twistedE6 f) (θ := θ) hθcent hDN
    (fun d hd => ggLiePartner_exists ht hf hpres hΓ hθc (hDN hd) (hDinn d hd))
  have hker_clause : ∀ a : ↥A, Θ a = 1 ↔ (a : X) ∈ Subgroup.centralizer (G₀ : Set X) := by
    intro a
    constructor
    · intro hΘa
      refine centralizes_of_trivial_bridge_action θ hpres.2.2.1 hθker (hDN a.2) ?_
      intro x hx
      have hh := (hΘ a).2 x hx
      rw [hΘa] at hh
      simpa using hh
    · intro hcent_a
      refine hθcent (Θ a) (hΘ a).1 ?_
      intro x
      have hxmem : (a : X) * (x : X) * (a : X)⁻¹ ∈ G₀ :=
        (Subgroup.mem_normalizer_iff.mp (hDN a.2) (x : X)).mp x.2
      have hh := (hΘ a).2 x hxmem
      have hcommx : (x : X) * (a : X) = (a : X) * (x : X) :=
        (Subgroup.mem_centralizer_iff.mp hcent_a) (x : X) x.2
      have hsub : (⟨(a : X) * (x : X) * (a : X)⁻¹, hxmem⟩ : ↥G₀) = x := by
        apply Subtype.ext
        show (a : X) * (x : X) * (a : X)⁻¹ = (x : X)
        rw [← hcommx]
        group
      rw [hsub] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh.symm
  exact ⟨θ, Θ, hθc, hθker, hθrange, fun a => (hΘ a).1, hker_clause, fun a => (hΘ a).2⟩

end CFSG.StandardType.LieKnownR2.ExcPos
