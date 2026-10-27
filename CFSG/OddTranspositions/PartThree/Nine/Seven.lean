module

public import CFSG.OddTranspositions.PartThree.Nine.SevenCore

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld.Bridge.Asc72
open CFSG.ProperTwoGeneratedCore.CosetNormalizerSinger (apply_eq_linear_add)
open scoped IsMulCommutative

private theorem exists_fixed_of_fieldPart {F : Type*} [Field F] [CharP F 2] (σ : F ≃+* F)
    (hσ : ∀ x, σ (σ x) = x) {c₀ : F} (hc₀ : σ c₀ ≠ c₀) {c β : F} (hβ : c * σ β = β) :
    ∃ x, c * σ x + β = x := by
  have hne : c₀ + σ c₀ ≠ 0 := by
    intro h
    apply hc₀
    rw [← sub_eq_zero, CharTwo.sub_eq_add, add_comm]
    exact h
  have hσs : σ (c₀ + σ c₀) = c₀ + σ c₀ := by rw [map_add, hσ, add_comm]
  have key : σ c₀ / (c₀ + σ c₀) + 1 = c₀ / (c₀ + σ c₀) := by
    rw [eq_div_iff hne, add_mul, div_mul_cancel₀ _ hne, one_mul, add_left_comm,
      CharTwo.add_self_eq_zero, add_zero]
  refine ⟨c₀ / (c₀ + σ c₀) * β, ?_⟩
  calc c * σ (c₀ / (c₀ + σ c₀) * β) + β =
        σ c₀ / σ (c₀ + σ c₀) * (c * σ β) + β := by
        rw [map_mul, map_div₀]
        ring
    _ = (σ c₀ / (c₀ + σ c₀) + 1) * β := by rw [hσs, hβ]; ring
    _ = c₀ / (c₀ + σ c₀) * β := by rw [key]

theorem lemma9_7 : Lemma9_7 := by
  intro G _ _ D hC hH _ _ h3 T S hTS _ _ Q hQ d hd e he hde hc hN
  obtain ⟨U, hU⟩ := exists_deltaSetup hC hH h3 T S hTS
  have := hU.isElementaryAbelian
  rw [hU.sylow_inter] at hQ hN
  obtain ⟨-, -, ⟨φ, -, hφ⟩, -⟩ := hU.affine h3
  obtain ⟨k, -, hk⟩ := hU.exists_card
  obtain ⟨ψ, hsemi, -, -⟩ := hU.exists_semilinear_coordinates_of_isRegularCore h3 hQ φ hφ hk
  set y : Subgroup.normalizer ((fun v : G => hC.d * v) '' (U : Set G)) := ⟨d * e, hN⟩
  have hy2 : y * y = 1 := Subtype.ext (by
    change d * e * (d * e) = 1
    rw [mul_assoc, ← mul_assoc e d e, ← hc.eq, mul_assoc, hC.setup.oddT.mul_self_eq_one he,
      mul_one, hC.setup.oddT.mul_self_eq_one hd])
  have hφ2 : φ y * φ y = 1 := by rw [← map_mul, hy2, map_one]
  have hφφ : ∀ w, φ y (φ y w) = w := fun w =>
    congrArg (fun g : Additive U ≃ᵃ[ZMod 2] Additive U => g w) hφ2
  have hℓℓ : ∀ w, (φ y).linear ((φ y).linear w) = w := fun w => by
    have h := congrArg AffineEquiv.linearHom hφ2
    rw [map_mul, map_one] at h
    exact congrArg (fun g : Additive U ≃ₗ[ZMod 2] Additive U => g w) h
  obtain ⟨c, σ, hcσ⟩ := hsemi y
  have hcc : (c : GaloisField 2 k) * σ c = 1 := by
    have h := hcσ ((φ y).linear (ψ.symm 1))
    rw [hℓℓ, LinearEquiv.apply_symm_apply, hcσ, LinearEquiv.apply_symm_apply, map_one,
      mul_one] at h
    exact h.symm
  have hσσ : ∀ x, σ (σ x) = x := fun x => by
    have h := hcσ ((φ y).linear (ψ.symm x))
    rw [hℓℓ, LinearEquiv.apply_symm_apply, hcσ, LinearEquiv.apply_symm_apply, map_mul,
      ← mul_assoc, hcc, one_mul] at h
    exact h.symm
  have hbb : (φ y).linear (φ y 0) = φ y 0 := by
    have h := apply_eq_linear_add (φ y) (φ y 0)
    rw [hφφ] at h
    have h2 : φ y 0 + φ y 0 = 0 := by
      rw [← two_smul (ZMod 2) (φ y 0), show (2 : ZMod 2) = 0 by decide, zero_smul]
    exact add_right_cancel (h.symm.trans h2.symm)
  have hβ : (c : GaloisField 2 k) * σ (ψ (φ y 0)) = ψ (φ y 0) := by rw [← hcσ, hbb]
  by_cases hσ1 : ∀ x, σ x = x
  ·
    rw [hσ1] at hcc
    have hc1 : (c : GaloisField 2 k) = 1 := by
      rcases mul_self_eq_one_iff.mp hcc with h | h
      · exact h
      · rwa [CharTwo.neg_eq] at h
    have hℓ1 : (φ y).linear = 1 := by
      refine LinearEquiv.ext fun w => ?_
      change (φ y).linear w = w
      apply ψ.injective
      rw [hcσ, hσ1, hc1, one_mul]
    exact hU.mem_regularCore_of_linear_eq_one h3 hQ φ hφ hℓ1
  ·
    push Not at hσ1
    obtain ⟨c₀, hc₀⟩ := hσ1
    obtain ⟨x₀, hx₀⟩ := exists_fixed_of_fieldPart σ hσσ hc₀ hβ
    have hfix : φ y (ψ.symm x₀) = ψ.symm x₀ := by
      apply ψ.injective
      rw [apply_eq_linear_add, map_add, hcσ, LinearEquiv.apply_symm_apply]
      exact hx₀
    have hδ : hC.d * ((Additive.toMul (ψ.symm x₀) : U) : G) ∈
        (fun v : G => hC.d * v) '' (U : Set G) := ⟨_, (Additive.toMul (ψ.symm x₀)).2, rfl⟩
    have hδc : Commute (hC.d * ((Additive.toMul (ψ.symm x₀) : U) : G)) (d * e) := by
      have h := hφ y (Additive.toMul (ψ.symm x₀))
      rw [ofMul_toMul, hfix] at h
      change d * e * _ * (d * e)⁻¹ = _ at h
      exact (mul_inv_eq_iff_eq_mul.mp h).symm
    obtain ⟨-, -, -, hcent, -, -⟩ := hQ
    exact hcent (hU.mul_mem_centralizer_of_commute h3 hd he hde hc hN hδ hδc)

end CFSG.OddTranspositions.PartThree.Nine
