module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaOrthCoord
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsModel

public section

namespace CFSG.StandardType

namespace EnnolaFork

open Multiplicative NbrFrameOne SpCoord NbrOrth

variable {p k : ℕ}

theorem permAut_swap_funMultiplicative (i j : Fin k) (f : Multiplicative (Fin k → ZMod p)) :
    permAut (Equiv.swap i j) (MulEquiv.funMultiplicative (Fin k) (ZMod p) f) =
      MulEquiv.funMultiplicative (Fin k) (ZMod p) (swapAut i j f) := by
  obtain ⟨t, rfl⟩ := ofAdd.surjective f
  funext l
  rw [SpCoord.permAut_apply, swapAut_apply]
  simp [MulEquiv.funMultiplicative, Equiv.swap_inv]

theorem dinv_permAut_swap_funMultiplicative {i j : Fin k} (hij : i ≠ j)
    (f : Multiplicative (Fin k → ZMod p)) :
    dinv i j (permAut (Equiv.swap i j) (MulEquiv.funMultiplicative (Fin k) (ZMod p) f)) =
      MulEquiv.funMultiplicative (Fin k) (ZMod p) (antiSwapAut i j f) := by
  obtain ⟨t, rfl⟩ := ofAdd.surjective f
  funext l
  rw [OrthNs.dinv_apply_eq, permAut_swap_funMultiplicative, swapAut_apply,
    antiSwapAut_apply hij]
  by_cases hl : l = i
  · subst hl
    simp [hij, Equiv.swap_apply_left, MulEquiv.funMultiplicative, ofAdd_neg]
  · by_cases hl2 : l = j
    · subst hl2
      simp [hl, hij, Equiv.swap_apply_right, MulEquiv.funMultiplicative, ofAdd_neg]
    · simp [hl, hl2, Equiv.swap_apply_of_ne_of_ne hl hl2, MulEquiv.funMultiplicative]

theorem forkAut_induced {R : Type} [Group R] (τ : (Fin k → Multiplicative (ZMod p)) →* R)
    (hd : ∀ i j : Fin k, i ≠ j → ∃ w : R, ∀ f, w * τ f * w⁻¹ = τ (dinv i j f))
    (hP : ∀ σ : Equiv.Perm (Fin k), ∃ w : R, ∀ f, w * τ f * w⁻¹ = τ (permAut σ f))
    (a b c d : Fin k) (hcd : c ≠ d) (j : Fin 4) :
    ∃ w : R, ∀ f : Multiplicative (Fin k → ZMod p),
      w⁻¹ * τ (MulEquiv.funMultiplicative (Fin k) (ZMod p) f) * w =
        τ (MulEquiv.funMultiplicative (Fin k) (ZMod p) (forkAut a b c d j f)) := by
  fin_cases j
  · obtain ⟨w₀, hw₀⟩ := hP (Equiv.swap b c)
    refine ⟨w₀⁻¹, fun f => ?_⟩
    change (w₀⁻¹)⁻¹ * τ (MulEquiv.funMultiplicative (Fin k) (ZMod p) f) * w₀⁻¹ =
      τ (MulEquiv.funMultiplicative (Fin k) (ZMod p) (swapAut b c f))
    rw [inv_inv, ← permAut_swap_funMultiplicative b c f]
    exact hw₀ _
  · obtain ⟨w₀, hw₀⟩ := hP (Equiv.swap a b)
    refine ⟨w₀⁻¹, fun f => ?_⟩
    change (w₀⁻¹)⁻¹ * τ (MulEquiv.funMultiplicative (Fin k) (ZMod p) f) * w₀⁻¹ =
      τ (MulEquiv.funMultiplicative (Fin k) (ZMod p) (swapAut a b f))
    rw [inv_inv, ← permAut_swap_funMultiplicative a b f]
    exact hw₀ _
  · obtain ⟨w₀, hw₀⟩ := hP (Equiv.swap c d)
    refine ⟨w₀⁻¹, fun f => ?_⟩
    change (w₀⁻¹)⁻¹ * τ (MulEquiv.funMultiplicative (Fin k) (ZMod p) f) * w₀⁻¹ =
      τ (MulEquiv.funMultiplicative (Fin k) (ZMod p) (swapAut c d f))
    rw [inv_inv, ← permAut_swap_funMultiplicative c d f]
    exact hw₀ _
  · obtain ⟨w₁, hw₁⟩ := hd c d hcd
    obtain ⟨w₂, hw₂⟩ := hP (Equiv.swap c d)
    refine ⟨(w₁ * w₂)⁻¹, fun f => ?_⟩
    change ((w₁ * w₂)⁻¹)⁻¹ * τ (MulEquiv.funMultiplicative (Fin k) (ZMod p) f) *
        (w₁ * w₂)⁻¹ =
      τ (MulEquiv.funMultiplicative (Fin k) (ZMod p) (antiSwapAut c d f))
    rw [inv_inv]
    calc (w₁ * w₂) * τ (MulEquiv.funMultiplicative (Fin k) (ZMod p) f) * (w₁ * w₂)⁻¹
        = w₁ * (w₂ * τ (MulEquiv.funMultiplicative (Fin k) (ZMod p) f) * w₂⁻¹) * w₁⁻¹ := by
          group
      _ = w₁ * τ (permAut (Equiv.swap c d)
            (MulEquiv.funMultiplicative (Fin k) (ZMod p) f)) * w₁⁻¹ := by rw [hw₂]
      _ = w₁ * τ (MulEquiv.funMultiplicative (Fin k) (ZMod p) (swapAut c d f)) * w₁⁻¹ := by
          rw [permAut_swap_funMultiplicative c d f]
      _ = τ (dinv c d (MulEquiv.funMultiplicative (Fin k) (ZMod p) (swapAut c d f))) :=
          hw₁ _
      _ = τ (dinv c d (permAut (Equiv.swap c d)
            (MulEquiv.funMultiplicative (Fin k) (ZMod p) f))) := by
          rw [permAut_swap_funMultiplicative c d f]
      _ = τ (MulEquiv.funMultiplicative (Fin k) (ZMod p) (antiSwapAut c d f)) := by
          rw [dinv_permAut_swap_funMultiplicative hcd f]

end EnnolaFork

end CFSG.StandardType

end
