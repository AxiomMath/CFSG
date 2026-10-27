module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.OmSemi
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.OmSelf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.OmSkewSq
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.OmSkewNs
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.SignalizerFunctorTheorem.NonLocal.Orth
open CFSG.ComponentClassification CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalInvolutionRepresentation

variable {K : Type} [Field K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}


private theorem conj_inv_eichler
    (hex : ∀ u w : Fin d → K, ∃ x : matrixDerived Q,
      matrixLinearIso (d := d) (K := K) x.val = eichler Q u w)
    {g : similarityPairs Q} {u w : Fin d → K} (huw : polar Q u w = 0)
    (hE : eichler Q (coordinateSemilinearMap g.val u)
      ((multiplier Q g : K)⁻¹ • coordinateSemilinearMap g.val w) = eichler Q u (-w)) :
    matrixProjectiveConjugationHom Q g (matrixProjectiveProjection Q (eMat hex u w)) =
      (matrixProjectiveProjection Q (eMat hex u w))⁻¹ := by
  rw [matrixProjectiveConjugationHom_eMat, eMat_eq_of_eichler_eq hex hE, ← map_inv,
    eMat_inv hex huw]

private theorem exists_heis_class_of_skewNonsquare [Finite K] (hK2 : ringChar K ≠ 2) (hd : 5 ≤ d)
    (hex : ∀ u w : Fin d → K, ∃ x : matrixDerived Q,
      matrixLinearIso (d := d) (K := K) x.val = eichler Q u w)
    {g : similarityPairs Q}
    (hS : ∀ v, coordinateSemilinearMap g.val v = g.val.left.val *ᵥ v)
    (hAQ : ∀ v, Q (g.val.left.val *ᵥ v) = (multiplier Q g : K) * Q v)
    (hAA' : g.val.left.val * g.val.left.val = (-(multiplier Q g : K)) • 1)
    (hsq : ∀ l : K, l ^ 2 ≠ -(multiplier Q g : K)) :
    ∃ x : matrixProjectiveDerived Q, matrixProjectiveConjugationHom Q g x = x⁻¹ ∧
      ∃ u₁ u₂ z₁ z₂ : Fin d → K, u₁ ≠ 0 ∧ Q u₁ = 0 ∧ Q u₂ = 0 ∧ polar Q u₁ u₂ = 0 ∧
        u₂ ∉ Submodule.span K {u₁} ∧ polar Q u₁ z₁ = 0 ∧ polar Q u₂ z₁ = 0 ∧
        polar Q u₁ z₂ = 0 ∧ polar Q u₂ z₂ = 0 ∧ polar Q z₁ z₂ = 0 ∧
        z₁ ∉ Submodule.span K {u₁, u₂} ∧
        x = matrixProjectiveProjection Q (eMat hex u₁ z₁ * eMat hex u₂ z₂) := by
  have hμ0 : (multiplier Q g : K) ≠ 0 := Units.ne_zero _
  obtain ⟨u, z, hu0, hu, hAu, huAu, h1, h2, h3', h4, h5, hz⟩ :=
    exists_heis_inv_skewNonsquare hK2 hd hμ0 hAQ hAA' hsq
  have hQAu : Q (g.val.left.val *ᵥ u) = 0 := by rw [hAQ, hu, mul_zero]
  refine ⟨matrixProjectiveProjection Q (eMat hex u (g.val.left.val *ᵥ z) *
    eMat hex (g.val.left.val *ᵥ u) z), ?_, u, g.val.left.val *ᵥ u, g.val.left.val *ᵥ z, z,
    hu0, hu, hQAu, huAu, hAu, h1, h2, h3', h4, h5, hz, rfl⟩
  have hAAv' : ∀ v, g.val.left.val *ᵥ (g.val.left.val *ᵥ v) =
      (-(multiplier Q g : K)) • v := by
    intro v
    rw [mulVec_mulVec, hAA', smul_mulVec, one_mulVec]
  have hneg : ∀ v : Fin d → K, (multiplier Q g : K)⁻¹ • ((-(multiplier Q g : K)) • v) = -v := by
    intro v
    rw [smul_smul, mul_neg, inv_mul_cancel₀ hμ0, neg_one_smul]
  have hneg' : ∀ v : Fin d → K, (-(multiplier Q g : K)) • ((multiplier Q g : K)⁻¹ • v) = -v := by
    intro v
    rw [smul_smul, neg_mul, mul_inv_cancel₀ hμ0, neg_one_smul]
  rw [map_mul, map_mul, matrixProjectiveConjugationHom_eMat,
    matrixProjectiveConjugationHom_eMat, hS, hS, hS, hS, hAAv', hAAv', hneg,
    eMat_smul_left, hneg', ← map_mul, ← map_mul, ← map_inv, _root_.mul_inv_rev,
    eMat_inv hex h4, eMat_inv hex h1]

private theorem right_one_data [Finite K] (hd : 5 ≤ d) (hQ : (polarBilin Q).Nondegenerate)
    {g : similarityPairs Q} (hσ : g.val.right = 1)
    (hc : ∃ c : Kˣ, g.val.left * CatalogueBHigherLinearField.glFieldAut (Fin d) K g.val.right
      g.val.left = Matrix.GeneralLinearGroup.scalar (Fin d) c)
    (hns : g.val.right = 1 → ∀ a : Kˣ,
      GeneralLinearGroup.scalar (Fin d) a ≠ g.val.left) :
    ∃ c : K, (∀ v, coordinateSemilinearMap g.val v = g.val.left.val *ᵥ v) ∧
      (∀ v, Q (g.val.left.val *ᵥ v) = (multiplier Q g : K) * Q v) ∧
      g.val.left.val * g.val.left.val = c • 1 ∧ (∀ a : K, g.val.left.val ≠ a • 1) ∧
      ((multiplier Q g : K) = c ∨ (multiplier Q g : K) = -c) := by
  have hS : ∀ v, coordinateSemilinearMap g.val v = g.val.left.val *ᵥ v := by
    intro v
    rw [coordinateSemilinearMap_apply, hσ]
    rfl
  have hAQ : ∀ v, Q (g.val.left.val *ᵥ v) = (multiplier Q g : K) * Q v := by
    intro v
    rw [← hS, multiplier_spec, hσ]
    rfl
  obtain ⟨c, hc⟩ := hc
  have hAA : g.val.left.val * g.val.left.val = (c : K) • 1 := by
    rw [hσ, map_one] at hc
    have h1 := congrArg (fun B : GL (Fin d) K => (B : Matrix (Fin d) (Fin d) K)) hc
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at h1
    rw [smul_one_eq_diagonal, ← scalar_apply]
    exact h1
  have hns' : ∀ a : K, g.val.left.val ≠ a • 1 := by
    intro a ha
    have ha0 : a ≠ 0 := by
      rintro rfl
      have h1 := congrArg (fun B : GL (Fin d) K => (B : Matrix (Fin d) (Fin d) K))
        (mul_inv_cancel g.val.left)
      simp only [Units.val_mul, Units.val_one, ha, zero_smul, Matrix.zero_mul] at h1
      exact zero_ne_one (congrFun (congrFun h1 ⟨0, by omega⟩) ⟨0, by omega⟩ |>.trans
        (Matrix.one_apply_eq _))
    refine hns hσ (Units.mk0 a ha0) (Units.ext ?_)
    rw [GeneralLinearGroup.coe_scalar, Units.val_mk0, ha, smul_one_eq_diagonal, scalar_apply]
  have hAAv : ∀ v, g.val.left.val *ᵥ (g.val.left.val *ᵥ v) = (c : K) • v := by
    intro v
    rw [mulVec_mulVec, hAA, smul_mulVec, one_mulVec]
  have hμc : (multiplier Q g : K) = c ∨ (multiplier Q g : K) = -c := by
    obtain ⟨v, hv⟩ := exists_map_ne_zero_of_nondegenerate (by omega) hQ
    have h1 := hAQ (g.val.left.val *ᵥ v)
    rw [hAAv, hAQ, QuadraticMap.map_smul] at h1
    have h2 : ((multiplier Q g : K) - c) * ((multiplier Q g : K) + c) = 0 := by
      have h3 : (((multiplier Q g : K) * (multiplier Q g : K)) - (c : K) * c) * Q v = 0 := by
        linear_combination -1 * h1
      have h4 := (mul_eq_zero.mp h3).resolve_right hv
      linear_combination h4
    rcases mul_eq_zero.mp h2 with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  exact ⟨c, hS, hAQ, hAA, hns', hμc⟩

private theorem exists_inv_omega_of_right_eq_one [Finite K] (hK2 : ringChar K ≠ 2) (hd : 5 ≤ d)
    (hQ : (polarBilin Q).Nondegenerate)
    (hex : ∀ u w : Fin d → K, ∃ x : matrixDerived Q,
      matrixLinearIso (d := d) (K := K) x.val = eichler Q u w)
    {g : similarityPairs Q} (hσ : g.val.right = 1)
    (hc : ∃ c : Kˣ, g.val.left * CatalogueBHigherLinearField.glFieldAut (Fin d) K g.val.right
      g.val.left = Matrix.GeneralLinearGroup.scalar (Fin d) c)
    (hns : g.val.right = 1 → ∀ a : Kˣ,
      GeneralLinearGroup.scalar (Fin d) a ≠ g.val.left) :
    ∃ x : matrixProjectiveDerived Q, matrixProjectiveConjugationHom Q g x = x⁻¹ ∧
      ((∃ u w : Fin d → K, u ≠ 0 ∧ Q u = 0 ∧ polar Q u w = 0 ∧
          w ∉ Submodule.span K {u} ∧ x = matrixProjectiveProjection Q (eMat hex u w)) ∨
        ∃ u₁ u₂ z₁ z₂ : Fin d → K, u₁ ≠ 0 ∧ Q u₁ = 0 ∧ Q u₂ = 0 ∧ polar Q u₁ u₂ = 0 ∧
          u₂ ∉ Submodule.span K {u₁} ∧ polar Q u₁ z₁ = 0 ∧ polar Q u₂ z₁ = 0 ∧
          polar Q u₁ z₂ = 0 ∧ polar Q u₂ z₂ = 0 ∧ polar Q z₁ z₂ = 0 ∧
          z₁ ∉ Submodule.span K {u₁, u₂} ∧
          x = matrixProjectiveProjection Q (eMat hex u₁ z₁ * eMat hex u₂ z₂)) := by
  have hG1 : ∀ {u w : Fin d → K}, u ≠ 0 → Q u = 0 → polar Q u w = 0 →
      w ∉ Submodule.span K {u} →
      eichler Q (coordinateSemilinearMap g.val u)
        ((multiplier Q g : K)⁻¹ • coordinateSemilinearMap g.val w) = eichler Q u (-w) →
      ∃ x : matrixProjectiveDerived Q, matrixProjectiveConjugationHom Q g x = x⁻¹ ∧
        (∃ u w : Fin d → K, u ≠ 0 ∧ Q u = 0 ∧ polar Q u w = 0 ∧
          w ∉ Submodule.span K {u} ∧ x = matrixProjectiveProjection Q (eMat hex u w)) := by
    intro u w hu0 hu huw hw hE
    exact ⟨_, conj_inv_eichler hex huw hE, u, w, hu0, hu, huw, hw, rfl⟩
  obtain ⟨c, hS, hAQ, hAA, hns', hμc⟩ := right_one_data hd hQ hσ hc hns
  have hμ0 : (multiplier Q g : K) ≠ 0 := Units.ne_zero _
  rcases hμc with hμc | hμc
  ·
    obtain ⟨u, w, hu0, hu, huw, hw, hE⟩ := exists_eichler_inv_selfAdjoint hK2 hd
      hμ0 hAQ (by rw [hAA, hμc]) hns'
    obtain ⟨x, hx, hclass⟩ := hG1 hu0 hu huw hw (by rw [hS, hS]; exact hE)
    exact ⟨x, hx, Or.inl hclass⟩
  · by_cases hsq : ∃ l : K, l ^ 2 = -(multiplier Q g : K)
    ·
      obtain ⟨l, hl⟩ := hsq
      have hl0 : l ≠ 0 := by
        rintro rfl
        rw [zero_pow two_ne_zero, eq_comm, neg_eq_zero] at hl
        exact hμ0 hl
      obtain ⟨u, w, hu0, hu, huw, hw, hE⟩ := exists_eichler_inv_skewSquare hK2 (by omega)
        hl0 hAQ (by rw [hAA, hl, hμc, neg_neg]) (by rw [hl, neg_neg])
      obtain ⟨x, hx, hclass⟩ := hG1 hu0 hu huw hw (by rw [hS, hS]; exact hE)
      exact ⟨x, hx, Or.inl hclass⟩
    ·
      push Not at hsq
      have hAA' : g.val.left.val * g.val.left.val = (-(multiplier Q g : K)) • 1 := by
        rw [hAA, hμc, neg_neg]
      obtain ⟨x, hx, hclass⟩ :=
        exists_heis_class_of_skewNonsquare hK2 hd hex hS hAQ hAA' hsq
      exact ⟨x, hx, Or.inr hclass⟩

theorem exists_conj_inv_omega [Finite K] (hK2 : ringChar K ≠ 2) (hd : 5 ≤ d)
    (hQ : (polarBilin Q).Nondegenerate)
    (hex : ∀ u w : Fin d → K, ∃ x : matrixDerived Q,
      matrixLinearIso (d := d) (K := K) x.val = eichler Q u w)
    (hrep : SemilinearRepresentation Q) {α : MulAut (matrixProjectiveDerived Q)}
    (hα : orderOf α = 2) :
    ∃ (γ σ₀ : MulAut (matrixProjectiveDerived Q)) (x : matrixProjectiveDerived Q),
      α = γ * σ₀ * γ⁻¹ ∧ σ₀ x = x⁻¹ ∧
      ((∃ u w : Fin d → K, u ≠ 0 ∧ Q u = 0 ∧ polar Q u w = 0 ∧ w ∉ Submodule.span K {u} ∧
          x = matrixProjectiveProjection Q (eMat hex u w)) ∨
        ∃ u₁ u₂ z₁ z₂ : Fin d → K, u₁ ≠ 0 ∧ Q u₁ = 0 ∧ Q u₂ = 0 ∧ polar Q u₁ u₂ = 0 ∧
          u₂ ∉ Submodule.span K {u₁} ∧ polar Q u₁ z₁ = 0 ∧ polar Q u₂ z₁ = 0 ∧
          polar Q u₁ z₂ = 0 ∧ polar Q u₂ z₂ = 0 ∧ polar Q z₁ z₂ = 0 ∧
          z₁ ∉ Submodule.span K {u₁, u₂} ∧
          x = matrixProjectiveProjection Q (eMat hex u₁ z₁ * eMat hex u₂ z₂)) := by
  classical
  have hαα : α * α = 1 := by
    rw [← pow_two, ← hα]
    exact pow_orderOf_eq_one α
  have hα1 : α ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hα
    exact absurd hα (by norm_num)
  obtain ⟨β, g, hβ, hσ2, hc, hns, -⟩ := hrep.2 α hαα hα1
  have hconj : α = β * matrixProjectiveConjugationHom Q g * β⁻¹ := by
    rw [← hβ]
    group
  have hmain : ∃ x : matrixProjectiveDerived Q,
      matrixProjectiveConjugationHom Q g x = x⁻¹ ∧
      ((∃ u w : Fin d → K, u ≠ 0 ∧ Q u = 0 ∧ polar Q u w = 0 ∧
          w ∉ Submodule.span K {u} ∧ x = matrixProjectiveProjection Q (eMat hex u w)) ∨
        ∃ u₁ u₂ z₁ z₂ : Fin d → K, u₁ ≠ 0 ∧ Q u₁ = 0 ∧ Q u₂ = 0 ∧ polar Q u₁ u₂ = 0 ∧
          u₂ ∉ Submodule.span K {u₁} ∧ polar Q u₁ z₁ = 0 ∧ polar Q u₂ z₁ = 0 ∧
          polar Q u₁ z₂ = 0 ∧ polar Q u₂ z₂ = 0 ∧ polar Q z₁ z₂ = 0 ∧
          z₁ ∉ Submodule.span K {u₁, u₂} ∧
          x = matrixProjectiveProjection Q (eMat hex u₁ z₁ * eMat hex u₂ z₂)) := by
    by_cases hσ : g.val.right = 1
    · exact exists_inv_omega_of_right_eq_one hK2 hd hQ hex hσ hc hns
    ·
      obtain ⟨u, w, hu0, hu, huw, hw, hE⟩ :=
        exists_eichler_inv_semilinear hK2 (by omega) hQ g hσ2 hσ hc
      exact ⟨_, conj_inv_eichler hex huw hE, Or.inl ⟨u, w, hu0, hu, huw, hw, rfl⟩⟩
  obtain ⟨x, hxinv, hx⟩ := hmain
  exact ⟨β, matrixProjectiveConjugationHom Q g, x, hconj, hxinv, hx⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
