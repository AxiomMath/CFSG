module

public import CFSG.LocalAnalysis.StandardType.GGOrthFrameCore
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord
import CFSG.LocalAnalysis.StandardType.GGOrthFrameModelAux

public section

namespace CFSG.StandardType.QTwo

open CFSG.RankThree.Classical2 (orthDerived)

theorem qtwoDL1_oChart_mem_hyp_iff {p : ℕ} {G : Type} [Group G] [Finite G] {Bs L : Subgroup G}
    (Φ : OrthTorus.OrthFrameCore p Bs L) (hZ : Subgroup.center ↥L = ⊥)
    (hBN : Bs ≤ Subgroup.normalizer (L : Set G)) {i j k : Fin Φ.r}
    {w₀ w₁ : ↥(orthDerived Φ.Q)}
    (hw₀ : ∀ f : Fin Φ.r → Multiplicative (ZMod p),
      (w₀ : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (w₀ : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ =
        Φ.Δ.τ (SpCoord.permAut (Equiv.swap i j) f))
    (hw₁ : ∀ f : Fin Φ.r → Multiplicative (ZMod p),
      (w₁ : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (w₁ : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ =
        Φ.Δ.τ (SpCoord.permAut (Equiv.swap j k) f))
    {r₀ r₀' : MulAut ↥Bs}
    (hr₀ : ∀ s : ↥Bs, ((r₀ s : ↥Bs) : G) = Φ.ψ w₀ * (s : G) * (Φ.ψ w₀)⁻¹)
    (hr₀' : ∀ s : ↥Bs, ((r₀' s : ↥Bs) : G) = Φ.ψ w₁ * (s : G) * (Φ.ψ w₁)⁻¹) (b : ↥Bs) :
    (b : G) ∈ ggHyperplane Bs r₀ ⊓ ggHyperplane Bs r₀' ↔
      ∃ f : Fin Φ.r → Multiplicative (ZMod p),
        (Φ.β b : Φ.V ≃ₗ[Φ.F] Φ.V) = Φ.Δ.τ f ∧ f i = f j ∧ f j = f k := by
  constructor
  · intro hb
    rw [Subgroup.mem_inf] at hb
    obtain ⟨h0, h1⟩ := hb
    obtain ⟨f, hf⟩ : ∃ f : Fin Φ.r → Multiplicative (ZMod p),
        Φ.Δ.τ f = (Φ.β b : Φ.V ≃ₗ[Φ.F] Φ.V) := by
      have hmem : (Φ.β b : Φ.V ≃ₗ[Φ.F] Φ.V) ∈ Φ.A := Φ.hβA b
      rwa [← Φ.Δ.τ_range] at hmem
    refine ⟨f, hf.symm, ?_, ?_⟩
    · obtain ⟨b', hb', hcomm⟩ :=
        (mem_ggHyperplane_iff_comm Φ.ψ Φ.β Φ.hinj Φ.hcompat hr₀ (b : G)).mp h0
      rw [show b' = b from Subtype.ext hb'] at hcomm
      have hconj : w₀ * Φ.β b * w₀⁻¹ = Φ.β b := by
        rw [hcomm]; group
      have hcoe := congrArg (fun x : ↥(orthDerived Φ.Q) => (x : Φ.V ≃ₗ[Φ.F] Φ.V)) hconj
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hcoe
      rw [← hf] at hcoe
      have hτ : (w₀ : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (w₀ : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ =
          Φ.Δ.τ f := by simpa using hcoe
      have hfix : SpCoord.permAut (Equiv.swap i j) f = f := by
        apply Φ.Δ.τ_inj
        rw [← hw₀ f]
        exact hτ
      exact OrthTorus.ggOFM_eq_of_permAut_swap_eq_self hfix
    · obtain ⟨b', hb', hcomm⟩ :=
        (mem_ggHyperplane_iff_comm Φ.ψ Φ.β Φ.hinj Φ.hcompat hr₀' (b : G)).mp h1
      rw [show b' = b from Subtype.ext hb'] at hcomm
      have hconj : w₁ * Φ.β b * w₁⁻¹ = Φ.β b := by
        rw [hcomm]; group
      have hcoe := congrArg (fun x : ↥(orthDerived Φ.Q) => (x : Φ.V ≃ₗ[Φ.F] Φ.V)) hconj
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hcoe
      rw [← hf] at hcoe
      have hτ : (w₁ : Φ.V ≃ₗ[Φ.F] Φ.V) * Φ.Δ.τ f * (w₁ : Φ.V ≃ₗ[Φ.F] Φ.V)⁻¹ =
          Φ.Δ.τ f := by simpa using hcoe
      have hfix : SpCoord.permAut (Equiv.swap j k) f = f := by
        apply Φ.Δ.τ_inj
        rw [← hw₁ f]
        exact hτ
      exact OrthTorus.ggOFM_eq_of_permAut_swap_eq_self hfix
  · rintro ⟨f, hf, hfi, hfjk⟩
    have hfix₁ : SpCoord.permAut (Equiv.swap i j) f = f :=
      OrthTorus.ggOFM_permAut_swap_eq_self_of_eq hfi
    have hfix₂ : SpCoord.permAut (Equiv.swap j k) f = f :=
      OrthTorus.ggOFM_permAut_swap_eq_self_of_eq hfjk
    rw [Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · apply (mem_ggHyperplane_iff_comm Φ.ψ Φ.β Φ.hinj Φ.hcompat hr₀ (b : G)).mpr
      refine ⟨b, rfl, ?_⟩
      apply mul_inv_eq_iff_eq_mul.mp
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hf, hw₀ f, hfix₁]
    · apply (mem_ggHyperplane_iff_comm Φ.ψ Φ.β Φ.hinj Φ.hcompat hr₀' (b : G)).mpr
      refine ⟨b, rfl, ?_⟩
      apply mul_inv_eq_iff_eq_mul.mp
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hf, hw₁ f, hfix₂]

end CFSG.StandardType.QTwo

end
