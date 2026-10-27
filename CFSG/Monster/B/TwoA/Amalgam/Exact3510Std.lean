module

public import CFSG.Monster.B.TwoA.Amalgam.DistTwoStd
public import CFSG.Monster.B.E6.StdF4Orbital
public import CFSG.Monster.B.Generic.Exact3510Spectral

public noncomputable section

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster.B.E6.StdF4 CFSG.LieType.Chevalley.C2E6Std
  CFSG.LieType.Chevalley.C2E6Std.FieldExtension

theorem conjOrbit_centralizer_inl
    (x y : Pts) :
    conjOrbit (Subgroup.centralizer {(SemidirectProduct.inl (x : stdGroup) : GStar)})
        (SemidirectProduct.inl (y : stdGroup)) =
      (fun z : Pts => (SemidirectProduct.inl (z : stdGroup) : GStar)) ''
        {z | relIdx x z = relIdx x y} := by
  ext q
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hc' : c * SemidirectProduct.inl (x : stdGroup) =
        SemidirectProduct.inl (x : stdGroup) * c :=
      Subgroup.mem_centralizer_singleton_iff.1 hc
    have hcx : c • x = x := by
      apply Subtype.ext
      have e : (SemidirectProduct.inl (starConj c x) : GStar) =
          SemidirectProduct.inl (x : stdGroup) := by
        rw [inl_starConj, hc', mul_inv_cancel_right]
      exact SemidirectProduct.inl_injective e
    refine ⟨c • y, ?_, ?_⟩
    · show relIdx x (c • y) = relIdx x y
      conv_lhs => rw [← hcx]
      exact relIdx_smul c x y
    · show SemidirectProduct.inl (starConj c y) = _
      exact inl_starConj c y
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨γ, hγx, hγy⟩ := exists_smul_pair (x := x) (y := y) (x' := x) (y' := z) hz.symm
    have hx' : γ * SemidirectProduct.inl (x : stdGroup) * γ⁻¹ =
        SemidirectProduct.inl (x : stdGroup) := by
      rw [← inl_starConj, ← coe_smul, hγx]
    refine ⟨γ, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      calc γ * SemidirectProduct.inl (x : stdGroup)
          = γ * SemidirectProduct.inl (x : stdGroup) * γ⁻¹ * γ := by group
        _ = SemidirectProduct.inl (x : stdGroup) * γ := by rw [hx']
    · rw [← inl_starConj, ← coe_smul, hγy]

theorem orbSize_inl_eq
    (x y : Pts) :
    orbSize (SemidirectProduct.inl (x : stdGroup)) (SemidirectProduct.inl (y : stdGroup)) =
      orbK (relIdx x y) := by
  rw [orbSize, conjOrbit_centralizer_inl,
    Set.ncard_image_of_injective _ fun a b h => Subtype.ext (SemidirectProduct.inl_injective h),
    ← card_relIdx (relIdx x y) x, ← Set.ncard_coe_finset]
  congr 1
  ext z
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq]

theorem relIdx_eq_two_of_orbK {i : Fin 5} (h : orbK i = 44352) : i = 2 := by
  revert h
  fin_cases i <;> decide

theorem relIdx_eq_four_of_orbK {i : Fin 5} (h : orbK i = 2097152) : i = 4 := by
  revert h
  fin_cases i <;> decide

theorem relIdx_eq_two_of_orbSize
    {x y : Pts}
    (h : orbSize (SemidirectProduct.inl (x : stdGroup)) (SemidirectProduct.inl (y : stdGroup)) =
      44352) : relIdx x y = 2 :=
  relIdx_eq_two_of_orbK ((orbSize_inl_eq x y).symm.trans h)

theorem relIdx_eq_four_of_orbSize
    {x y : Pts}
    (h : orbSize (SemidirectProduct.inl (x : stdGroup)) (SemidirectProduct.inl (y : stdGroup)) =
      2097152) : relIdx x y = 4 :=
  relIdx_eq_four_of_orbK ((orbSize_inl_eq x y).symm.trans h)

theorem sum_smul_orbA_apply
    (c : Fin 5 → ℝ) (x y : Pts) :
    (∑ i, c i • orbA i) x y = c (relIdx x y) := by
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, orbA_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]

theorem orbP_zero_div : ((orbP 0 0 : ℝ) / orbK 0 = 1) ∧ ((orbP 0 2 : ℝ) / orbK 2 = 1 / 8) ∧
    ((orbP 0 4 : ℝ) / orbK 4 = 1 / 64) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [orbP, orbK] <;> norm_num

theorem orbP_one_div : ((orbP 1 0 : ℝ) / orbK 0 = 1) ∧ ((orbP 1 2 : ℝ) / orbK 2 = 1 / 528) ∧
    ((orbP 1 4 : ℝ) / orbK 4 = -1 / 4096) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [orbP, orbK] <;> norm_num

section Embedded

open CFSG.Monster.B.Generic

variable {V : Type*} [Fintype V] [DecidableEq V] (X : SimpleGraph V) [DecidableRel X.Adj]
  (φ : V → Pts)

omit [Fintype V] in
theorem submatrix_orbP_eq_of_relIdx
    (hφ : ∀ a b, relIdx (φ a) (φ b) = if a = b then 0 else if X.Adj a b then 2 else 4)
    (r : Fin 5) :
    (∑ i, ((orbP r i : ℝ) / orbK i) • orbA i).submatrix φ φ =
      levelMat X ((orbP r 2 : ℝ) / orbK 2) ((orbP r 4 : ℝ) / orbK 4) +
        ((orbP r 0 : ℝ) / orbK 0 - 1) • (1 : Matrix V V ℝ) := by
  ext a b
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.submatrix_apply,
    sum_smul_orbA_apply, hφ a b]
  simp only [levelMat, Matrix.of_apply]
  split_ifs <;> ring

omit [Fintype V] in
theorem posSemidef_levelMat_of_relIdx_zero
    (hφ : ∀ a b, relIdx (φ a) (φ b) = if a = b then 0 else if X.Adj a b then 2 else 4) :
    (levelMat X (1 / 8) (1 / 64)).PosSemidef := by
  have h := (posSemidef_orbP 0).submatrix φ
  rw [submatrix_orbP_eq_of_relIdx X φ hφ 0, orbP_zero_div.1, orbP_zero_div.2.1,
    orbP_zero_div.2.2, sub_self, zero_smul, add_zero] at h
  exact h

omit [Fintype V] in
theorem posSemidef_levelMat_of_relIdx_one
    (hφ : ∀ a b, relIdx (φ a) (φ b) = if a = b then 0 else if X.Adj a b then 2 else 4) :
    (levelMat X (1 / 528) (-1 / 4096)).PosSemidef := by
  have h := (posSemidef_orbP 1).submatrix φ
  rw [submatrix_orbP_eq_of_relIdx X φ hφ 1, orbP_one_div.1, orbP_one_div.2.1,
    orbP_one_div.2.2, sub_self, zero_smul, add_zero] at h
  exact h

theorem spectral_bounds_of_relIdx (hreg : X.IsRegularOfDegree 693)
    (hφ : ∀ a b, relIdx (φ a) (φ b) = if a = b then 0 else if X.Adj a b then 2 else 4) :
    (∀ μ : ℝ, Module.End.HasEigenvalue (Matrix.toLin' (X.adjMatrix ℝ)) μ → -9 ≤ μ) ∧
      Fintype.card V ≤ 10166 :=
  ⟨neg_nine_le_of_posSemidef X hreg (posSemidef_levelMat_of_relIdx_zero X φ hφ),
    card_le_of_posSemidef X hreg (posSemidef_levelMat_of_relIdx_one X φ hφ)⟩

end Embedded

end CFSG.Monster.B.TwoA.Amalgam
