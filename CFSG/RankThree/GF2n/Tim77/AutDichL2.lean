module

public import CFSG.CGT.Timmesfeld75.L2AutInvol
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Comparator.Defs

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG.CGT.Timmesfeld75
open scoped MatrixGroups

theorem autDichL2_eq_one_of_comm {F : Type} [Field F] [CharP F 2] {x : SL(2, F)}
    (hT : x * utriElt 1 = utriElt 1 * x) (hL : x * ltriElt 1 = ltriElt 1 * x) : x = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have e1 : x 1 0 = 0 := by
    have h := congrArg (fun g : SL(2, F) => g 0 0) hT
    simp only [mul_apply_00, utriElt_apply_00, utriElt_apply_01, utriElt_apply_10] at h
    linear_combination -h
  have e2 : x 0 1 = 0 := by
    have h := congrArg (fun g : SL(2, F) => g 0 0) hL
    simp only [mul_apply_00, ltriElt_apply_00, ltriElt_apply_01, ltriElt_apply_10] at h
    linear_combination h
  have e3 : x 0 0 = x 1 1 := by
    have h := congrArg (fun g : SL(2, F) => g 0 1) hT
    simp only [mul_apply_01, utriElt_apply_00, utriElt_apply_01, utriElt_apply_11] at h
    linear_combination h
  have hsq : (x 0 0 - 1) ^ 2 = 0 := by
    linear_combination sl2_det x + (x 0 0) * e3 + (x 0 1) * e1 + (1 - x 0 0) * h2
  have ha : x 0 0 = 1 := sub_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 hsq)
  exact sl2_ext (by rw [ha, one_apply_00]) (by rw [e2, one_apply_01])
    (by rw [e1, one_apply_10]) (by rw [← e3, ha, one_apply_11])

theorem autDichL2_utri_sq {F : Type} [Field F] [CharP F 2] :
    utriElt (1 : F) * utriElt 1 = 1 := by
  have h11 : (1 : F) + 1 = 0 := by
    rw [one_add_one_eq_two]
    exact CharTwo.two_eq_zero
  rw [← utriElt_add, h11, utriElt_zero]

theorem autDichL2_ltri_sq {F : Type} [Field F] [CharP F 2] :
    ltriElt (1 : F) * ltriElt 1 = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  apply sl2_ext
  · simp only [mul_apply_00, ltriElt_apply_00, ltriElt_apply_01, ltriElt_apply_10, one_apply_00]
    ring
  · simp only [mul_apply_01, ltriElt_apply_00, ltriElt_apply_01, ltriElt_apply_11, one_apply_01]
    ring
  · simp only [mul_apply_10, ltriElt_apply_00, ltriElt_apply_10, ltriElt_apply_11, one_apply_10]
    linear_combination h2
  · simp only [mul_apply_11, ltriElt_apply_01, ltriElt_apply_10, ltriElt_apply_11, one_apply_11]
    ring

theorem autDichL2_utri_ne_one {F : Type} [Field F] : utriElt (1 : F) ≠ 1 := by
  intro h
  have h01 : utriElt (1 : F) 0 1 = (1 : SL(2, F)) 0 1 := by rw [h]
  rw [utriElt_apply_01, one_apply_01] at h01
  exact one_ne_zero h01

theorem autDichL2_ltri_ne_one {F : Type} [Field F] : ltriElt (1 : F) ≠ 1 := by
  intro h
  have h10 : ltriElt (1 : F) 1 0 = (1 : SL(2, F)) 1 0 := by rw [h]
  rw [ltriElt_apply_10, one_apply_10] at h10
  exact one_ne_zero h10

theorem autDichL2_map_utri {F : Type} [Field F] (σ : F ≃+* F) :
    Matrix.SpecialLinearGroup.map (σ : F →+* F) (utriElt (1 : F)) = utriElt 1 := by
  rw [← sl2FieldAut_eq_map, sl2FieldAut_utriElt, map_one]

theorem autDichL2_map_ltri {F : Type} [Field F] (σ : F ≃+* F) :
    Matrix.SpecialLinearGroup.map (σ : F →+* F) (ltriElt (1 : F)) = ltriElt 1 := by
  rw [← sl2FieldAut_eq_map, sl2FieldAut_ltriElt, map_one]

theorem autDich_l2 {L : Type} [Group L] {f : ℕ} (hf : 2 ≤ f)
    (e : L ≃* CFSG.Theory.Comparator.PSL2Model f) (σ : MulAut L) (hσ : σ * σ = 1)
    {ā : L} (hā : orderOf ā = 2) (hfix : σ ā = ā) :
    (∃ τ : L, τ * τ = 1 ∧ τ * ā = ā * τ ∧ ∀ z, σ z = τ * z * τ⁻¹) ∨
      ∃ t : L, orderOf t = 2 ∧ σ t = t ∧ ¬ Commute ā t := by
  obtain ⟨E⟩ : Nonempty (L ≃* SL(2, GaloisField 2 f)) :=
    ⟨e.trans (pslMulEquivSL (F := GaloisField 2 f))⟩
  have hσσ : ∀ y, σ (σ y) = y := fun y => by
    have h : (σ * σ) y = (1 : MulAut L) y := by rw [hσ]
    exact h
  obtain ⟨φ, hφdef⟩ : ∃ φ : SL(2, GaloisField 2 f) ≃* SL(2, GaloisField 2 f),
      ∀ x, φ x = E (σ (E.symm x)) := ⟨E.symm.trans (σ.trans E), fun x => rfl⟩
  have hφ : ∀ x, φ (φ x) = x := fun x => by
    rw [hφdef, hφdef, E.symm_apply_apply, hσσ, E.apply_symm_apply]
  have hā1 : ā ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hā
    exact absurd hā (by norm_num)
  have hEā : E ā ≠ 1 := fun h => hā1 (E.injective (by rw [h, map_one]))
  rcases autInvol_inner_or_field φ hφ with ⟨g, hgg, hg⟩ | ⟨k, σ₀, -, hk⟩
  ·
    have hτ : ∀ z, σ z = E.symm g * z * (E.symm g)⁻¹ := fun z => by
      apply E.injective
      have h1 : φ (E z) = E (σ z) := by rw [hφdef, E.symm_apply_apply]
      rw [← h1, hg, map_mul, map_mul, map_inv, E.apply_symm_apply]
    refine Or.inl ⟨E.symm g, ?_, ?_, hτ⟩
    · rw [← map_mul, hgg, map_one]
    · have h2 : σ ā = E.symm g * ā * (E.symm g)⁻¹ := hτ ā
      rw [hfix] at h2
      exact mul_inv_eq_iff_eq_mul.1 h2.symm
  ·
    obtain ⟨a, ha_def⟩ : ∃ a : SL(2, GaloisField 2 f), a = k * E ā * k⁻¹ := ⟨_, rfl⟩
    have ha1 : a ≠ 1 := by
      intro h
      apply hEā
      calc E ā = k⁻¹ * (k * E ā * k⁻¹) * k := by group
        _ = 1 := by rw [← ha_def, h, mul_one, inv_mul_cancel]
    obtain ⟨t', ht'2, ht'1, ht'fix, ht'nc⟩ : ∃ t' : SL(2, GaloisField 2 f), t' * t' = 1 ∧
        t' ≠ 1 ∧ Matrix.SpecialLinearGroup.map (σ₀ : GaloisField 2 f →+* GaloisField 2 f) t' = t' ∧
        ¬ Commute a t' := by
      by_cases hT : Commute a (utriElt 1)
      · refine ⟨ltriElt 1, autDichL2_ltri_sq, autDichL2_ltri_ne_one, autDichL2_map_ltri σ₀, ?_⟩
        intro hL
        exact ha1 (autDichL2_eq_one_of_comm hT.eq hL.eq)
      · exact ⟨utriElt 1, autDichL2_utri_sq, autDichL2_utri_ne_one, autDichL2_map_utri σ₀, hT⟩
    have hsq0 : (k⁻¹ * t' * k) * (k⁻¹ * t' * k) = 1 := by
      calc (k⁻¹ * t' * k) * (k⁻¹ * t' * k) = k⁻¹ * (t' * t') * k := by group
        _ = 1 := by rw [ht'2, mul_one, inv_mul_cancel]
    have hne0 : k⁻¹ * t' * k ≠ 1 := by
      intro h
      apply ht'1
      calc t' = k * (k⁻¹ * t' * k) * k⁻¹ := by group
        _ = 1 := by rw [h, mul_one, mul_inv_cancel]
    have hfix0 : φ (k⁻¹ * t' * k) = k⁻¹ * t' * k := by
      have h1 := hk (k⁻¹ * t' * k)
      rw [show k * (k⁻¹ * t' * k) * k⁻¹ = t' by group, ht'fix] at h1
      calc φ (k⁻¹ * t' * k) = k⁻¹ * (k * φ (k⁻¹ * t' * k) * k⁻¹) * k := by group
        _ = k⁻¹ * t' * k := by rw [h1]
    refine Or.inr ⟨E.symm (k⁻¹ * t' * k), ?_, ?_, ?_⟩
    · apply orderOf_eq_prime
      · rw [sq, ← map_mul, hsq0, map_one]
      · intro h
        apply hne0
        have h' := congrArg E h
        rwa [E.apply_symm_apply, map_one] at h'
    · apply E.injective
      rw [← hφdef, hfix0, E.apply_symm_apply]
    · intro hc
      apply ht'nc
      have hc' := congrArg E hc.eq
      rw [map_mul E, map_mul E, E.apply_symm_apply] at hc'
      show a * t' = t' * a
      calc a * t' = k * (E ā * (k⁻¹ * t' * k)) * k⁻¹ := by rw [ha_def]; group
        _ = k * ((k⁻¹ * t' * k) * E ā) * k⁻¹ := by rw [hc']
        _ = t' * a := by rw [ha_def]; group

end CFSG.RankThree.GF2n.Tim77
