module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.UnitaryHeisenberg.Pair
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearData

public section

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ClassicalGroups.UnitaryFlag Matrix
open CFSG.SignalizerFunctorTheorem.McBride.UnitaryHeisenberg
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.UnitaryAut

variable {K : Type} [Field K]

theorem glAut_scalar (σ : K ≃+* K) (c : Kˣ) :
    glAut σ (GeneralLinearGroup.scalar (Fin 3) c) =
      GeneralLinearGroup.scalar (Fin 3) (Units.map (σ : K →* K) c) := by
  apply Units.ext
  rw [coe_glAut]
  ext i j
  simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.map_apply,
    Matrix.diagonal_apply, Units.coe_map, MonoidHom.coe_ofClass]
  split_ifs <;> simp

theorem commutator_mul_central {G : Type*} [Group G] {a b z₁ z₂ : G} (h1 : Commute z₁ (b * z₂))
    (h2 : Commute a z₂) : ⁅a * z₁, b * z₂⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul, commutatorElement_eq_one_iff_commute.mpr h1,
    mul_one, mul_inv_cancel, one_mul, commutatorElement_mul_right_eq_mul_conj,
    commutatorElement_eq_one_iff_commute.mpr h2, mul_one, mul_inv_cancel_right]

theorem commute_scalar_left (c : Kˣ) (g : GL (Fin 3) K) :
    Commute (GeneralLinearGroup.scalar (Fin 3) c) g :=
  (commute_scalar c g).symm

variable {ω : K}

theorem exists_scalar_of_commute (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) (O y : GL (Fin 3) K)
    (ha : Commute y (O * aGL hω * O⁻¹)) (hb : Commute y (O * bGL * O⁻¹)) :
    ∃ μ : Kˣ, y = GeneralLinearGroup.scalar (Fin 3) μ := by
  have h1 : Commute (O⁻¹ * y * O) (aGL hω) := commute_inv_conj ha
  have h2 : Commute (O⁻¹ * y * O) bGL := commute_inv_conj hb
  have ha' : ((O⁻¹ * y * O : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * aMat ω =
      aMat ω * ((O⁻¹ * y * O : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    simpa [coe_aGL] using congrArg Units.val h1.eq
  have hb' : ((O⁻¹ * y * O : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * bMat =
      bMat * ((O⁻¹ * y * O : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    simpa [coe_bGL] using congrArg Units.val h2.eq
  obtain ⟨c, hc⟩ := commutant hω hω1 ha' hb'
  have hOOi : (O : Matrix (Fin 3) (Fin 3) K) * ((O⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hy : (y : Matrix (Fin 3) (Fin 3) K) = c • 1 := by
    have : y = O * (O⁻¹ * y * O) * O⁻¹ := by group
    rw [this]
    simp only [Units.val_mul] at hc ⊢
    rw [show (O⁻¹ : GL (Fin 3) K).val * y.val * O.val = c • 1 from hc]
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hOOi]
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h0 : (y : Matrix (Fin 3) (Fin 3) K) * ((y⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [hy] at h0
    simp at h0
  exact ⟨Units.mk0 c hc0, Units.ext (by
    rw [hy]
    simp [GeneralLinearGroup.coe_scalar, Matrix.smul_one_eq_diagonal])⟩

theorem exists_scalar_of_mk_eq {X a : GL (Fin 3) K}
    (h : ProjGenLinGroup.mk X = ProjGenLinGroup.mk a) :
    ∃ u : Kˣ, X = a * GeneralLinearGroup.scalar (Fin 3) u := by
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h
  exact ⟨u⁻¹, by rw [map_inv]; exact eq_mul_inv_of_mul_eq hu⟩

theorem fix_of_mk_eq (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) (O : GL (Fin 3) K) (σ : K ≃+* K)
    (B : GL (Fin 3) K)
    (hBa : ProjGenLinGroup.mk (B * glAut σ (O * aGL hω * O⁻¹) * B⁻¹) =
      ProjGenLinGroup.mk (O * aGL hω * O⁻¹))
    (hBb : ProjGenLinGroup.mk (B * glAut σ (O * bGL * O⁻¹) * B⁻¹) =
      ProjGenLinGroup.mk (O * bGL * O⁻¹)) : σ ω = ω := by
  obtain ⟨u, hu⟩ := exists_scalar_of_mk_eq hBa
  obtain ⟨v, hv⟩ := exists_scalar_of_mk_eq hBb
  have H : IsHeisPair (O * aGL hω * O⁻¹) (O * bGL * O⁻¹) (ζGL hω) :=
    (isHeisPair_GL hω hω1).conj O
  have h1 : ⁅B * glAut σ (O * aGL hω * O⁻¹) * B⁻¹, B * glAut σ (O * bGL * O⁻¹) * B⁻¹⁆ =
      ζGL hω := by
    rw [hu, hv, commutator_mul_central (commute_scalar_left _ _) (commute_scalar_left _ _).symm,
      ← H.ζ_eq_commutator]
  have hζσ : glAut σ (ζGL hω) = GeneralLinearGroup.scalar (Fin 3)
      (Units.map (σ : K →* K) (Units.mk0 ω (ne_zero_of_pow_three hω))) := glAut_scalar σ _
  have h2 : ⁅B * glAut σ (O * aGL hω * O⁻¹) * B⁻¹, B * glAut σ (O * bGL * O⁻¹) * B⁻¹⁆ =
      glAut σ (ζGL hω) := by
    rw [← conjugate_commutatorElement, ← map_commutatorElement, ← H.ζ_eq_commutator, hζσ,
      ← (commute_scalar_left _ _).eq, mul_assoc, mul_inv_cancel, mul_one]
  have h3 : ζGL hω = glAut σ (ζGL hω) := h1.symm.trans h2
  rw [hζσ] at h3
  have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) h3
  simpa [ζGL, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using this.symm

theorem exists_mem_closure_of_mk_eq (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) (O : GL (Fin 3) K)
    (B : GL (Fin 3) K)
    (hBa : ProjGenLinGroup.mk (B * (O * aGL hω * O⁻¹) * B⁻¹) =
      ProjGenLinGroup.mk (O * aGL hω * O⁻¹))
    (hBb : ProjGenLinGroup.mk (B * (O * bGL * O⁻¹) * B⁻¹) =
      ProjGenLinGroup.mk (O * bGL * O⁻¹)) :
    ∃ e ∈ Subgroup.closure {O * aGL hω * O⁻¹, O * bGL * O⁻¹},
      ∃ μ : Kˣ, B = e * GeneralLinearGroup.scalar (Fin 3) μ := by
  obtain ⟨u, hu⟩ := exists_scalar_of_mk_eq hBa
  obtain ⟨v, hv⟩ := exists_scalar_of_mk_eq hBb
  set a := O * aGL hω * O⁻¹ with ha_def
  set b := O * bGL * O⁻¹ with hb_def
  have H : IsHeisPair a b (ζGL hω) := (isHeisPair_GL hω hω1).conj O
  have hdeta : GeneralLinearGroup.det a = 1 := by
    rw [ha_def, map_mul, map_mul, map_inv, mul_comm (GeneralLinearGroup.det O), mul_assoc,
      mul_inv_cancel, mul_one]
    exact Units.ext (by rw [GeneralLinearGroup.val_det_apply, coe_aGL, det_aMat hω]; rfl)
  have hdetb : GeneralLinearGroup.det b = 1 := by
    rw [hb_def, map_mul, map_mul, map_inv, mul_comm (GeneralLinearGroup.det O), mul_assoc,
      mul_inv_cancel, mul_one]
    exact Units.ext (by rw [GeneralLinearGroup.val_det_apply, coe_bGL, det_bMat]; rfl)
  have hcub : ∀ (x : GL (Fin 3) K) (w : Kˣ), GeneralLinearGroup.det x = 1 →
      B * x * B⁻¹ = x * GeneralLinearGroup.scalar (Fin 3) w →
      GeneralLinearGroup.scalar (Fin 3) w ∈ Subgroup.zpowers (ζGL hω) := by
    intro x w hx hxw
    have h1 := congrArg GeneralLinearGroup.det hxw
    rw [map_mul, map_mul, map_inv, mul_comm (GeneralLinearGroup.det B), mul_assoc, mul_inv_cancel,
      mul_one, hx, map_mul, hx, GeneralLinearGroup.det_scalar, Fintype.card_fin, one_mul] at h1
    have h3 : (w : K) ^ 3 = 1 := by
      have := congrArg (fun z : Kˣ => (z : K)) h1
      simpa using this.symm
    refine mem_zpowers_ζGL_of_scalar hω hω1 (c := (w : K)) ?_ ?_
    · simp [GeneralLinearGroup.coe_scalar, Matrix.smul_one_eq_diagonal]
    · simp [GeneralLinearGroup.coe_scalar, h3]
  obtain ⟨s, hs⟩ := H.exists_ζ_pow (hcub a u hdeta hu)
  obtain ⟨t, ht⟩ := H.exists_ζ_pow (hcub b v hdetb hv)
  obtain ⟨e₀, he1, he2⟩ := Heis3.exists_comm_eq s t
  have h1 : ⁅H.Φ e₀, a⁆ = ⁅B, a⁆ := by
    have := congrArg H.Φ he1
    rw [map_commutatorElement, H.Φ_a₀, map_pow, H.Φ_ζ₀] at this
    rw [this, ← hs, commutatorElement_def, hu, ← GeneralLinearGroup.scalar_commute u a,
      mul_inv_cancel_right]
  have h2 : ⁅H.Φ e₀, b⁆ = ⁅B, b⁆ := by
    have := congrArg H.Φ he2
    rw [map_commutatorElement, H.Φ_b₀, map_pow, H.Φ_ζ₀] at this
    rw [this, ← ht, commutatorElement_def, hv, ← GeneralLinearGroup.scalar_commute v b,
      mul_inv_cancel_right]
  obtain ⟨μ, hμ⟩ := exists_scalar_of_commute hω hω1 O _ (IsHeisPair.commute_of_commutator_eq h1)
    (IsHeisPair.commute_of_commutator_eq h2)
  refine ⟨H.Φ e₀, ?_, μ, ?_⟩
  · rw [← H.E_eq_closure]
    exact ⟨e₀, rfl⟩
  · rw [← hμ]
    group

end CFSG.SignalizerFunctorTheorem.McBride.UnitaryAut
