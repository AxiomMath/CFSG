module

public import CFSG.RankThree.PartTwo.KFacts.AutPSp4Even
import CFSG.RankThree.PartTwo.KFacts.AutPSLOrderThree
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoGeneration
import CFSG.RankThree.Classical.SemilinearFixedBasis
import CFSG.GroupTheory.ABGLocalTools.SL2FieldAutSemilinear

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open Matrix

section Index

variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_isUnit_det_fixed_index {ℓ e : ℕ} (hℓ : ℓ.Prime) (he : 1 ≤ e)
    (hk : Nat.card k = ℓ ^ e) (σ : k ≃+* k) {h : ℕ} (hσ : orderOf σ = h)
    (A' : Matrix ι ι k) (hA' : IsUnit A'.det)
    (hper : ∀ v : ι → k, (fun w : ι → k => A' *ᵥ (σ ∘ w))^[h] v = v) :
    ∃ B : Matrix ι ι k, IsUnit B.det ∧ A' * B.map σ = B := by
  let Aeq : (ι → k) ≃ₗ[k] (ι → k) :=
    Matrix.toLinearEquiv' A' (Matrix.invertibleOfIsUnitDet A' hA')
  let T : (ι → k) ≃+ (ι → k) :=
    (AddEquiv.piCongrRight fun _ => σ.toAddEquiv).trans Aeq.toAddEquiv
  have hT : ∀ v, T v = A' *ᵥ (σ ∘ v) := fun v => by
    change Aeq (fun i => σ (v i)) = _
    rw [← LinearEquiv.coe_coe, Matrix.toLinearEquiv'_apply, Matrix.toLin'_apply]
    rfl
  have hTfun : (⇑T) = fun w : ι → k => A' *ᵥ (σ ∘ w) := funext hT
  have ha : ∀ (c : k) (v : ι → k), T (c • v) = σ c • T v := fun c v => by
    rw [hT, hT, ← Matrix.mulVec_smul]
    congr 1
    funext i
    simp
  have hah : ∀ v, (⇑T)^[h] v = v := fun v => by
    rw [hTfun]
    exact hper v
  obtain ⟨-, -, -, -, b, hb, -⟩ :=
    CFSG.RankThree.Classical.semilinear_fixed_basis hℓ he hk σ hσ
      (Module.finrank_fintype_fun_eq_card k) T ha hah
  set b' := b.reindex (Fintype.equivFin ι).symm with hb'
  have hb'fix : ∀ j, T (b' j) = b' j := fun j => by
    rw [hb', Module.Basis.reindex_apply]
    exact hb _
  refine ⟨(Pi.basisFun k ι).toMatrix b', ?_, ?_⟩
  · rw [← Module.Basis.det_apply]
    exact (Pi.basisFun k ι).isUnit_det b'
  · ext i j
    have h1 := congrFun (hb'fix j) i
    rw [hT] at h1
    rw [Module.Basis.toMatrix_apply, Pi.basisFun_repr, ← h1, Matrix.mul_apply, Matrix.mulVec,
      dotProduct]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.map_apply, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rfl

omit [DecidableEq ι] in
theorem map_mul_ringEquiv' (σ : k ≃+* k) (X Y : Matrix ι ι k) :
    (X * Y).map σ = X.map σ * Y.map σ :=
  Matrix.map_mul (f := (σ : k →+* k))

omit [Fintype ι] in
theorem map_one_ringEquiv' (σ : k ≃+* k) : (1 : Matrix ι ι k).map σ = 1 :=
  Matrix.map_one _ (map_zero σ) (map_one σ)

omit [Fintype ι] [DecidableEq ι] in
theorem map_smul_ringEquiv' (σ : k ≃+* k) (a : k) (X : Matrix ι ι k) :
    (a • X).map σ = σ a • X.map σ := by
  ext i j
  simp

omit [Fintype ι] [DecidableEq ι] in
theorem map_map_ringEquiv' (σ τ : k ≃+* k) (X : Matrix ι ι k) :
    (X.map τ).map σ = X.map ⇑(σ * τ) := by
  rw [Matrix.map_map]
  rfl

omit [Fintype ι] [DecidableEq ι] in
theorem eq_one_of_smul_eq_self' {a : k} {X : Matrix ι ι k} (hX : X ≠ 0) (h1 : a • X = X) :
    a = 1 :=
  smul_left_injective k hX (h1.trans (one_smul k X).symm)

theorem exists_mul_map_eq_scalar_mul_of_orderOf_eq_three_index [Finite k] [Nonempty ι]
    {σ : k ≃+* k} (hσ : orderOf σ = 3) (A : GL ι k) {c : kˣ}
    (hc : GeneralLinearGroup.scalar ι c = A * GeneralLinearGroup.map (σ : k →+* k) A *
      GeneralLinearGroup.map ((σ * σ : k ≃+* k) : k →+* k) A) :
    ∃ (H : GL ι k) (d : kˣ), A * GeneralLinearGroup.map (σ : k →+* k) H =
      GeneralLinearGroup.scalar ι d * H := by
  classical
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ, pow_orderOf_eq_one]
  have hσσσ : σ * σ * σ = 1 := by rw [← hσ3, pow_succ, pow_two]
  have hσx : ∀ x, σ (σ (σ x)) = x := fun x => iterate_three_apply_of_pow hσ3 x
  set M : Matrix ι ι k := (A : Matrix ι ι k) with hM
  have hmap : ∀ (τ : k ≃+* k) (X : GL ι k),
      ((GeneralLinearGroup.map (τ : k →+* k) X : GL ι k) : Matrix ι ι k) =
        (X : Matrix ι ι k).map τ := fun _ _ => rfl
  have hN : M * M.map σ * M.map ⇑(σ * σ) = (c : k) • (1 : Matrix ι ι k) := by
    have h := congrArg (fun X : GL ι k => (X : Matrix ι ι k)) hc
    simp only [Units.val_mul, hmap, GeneralLinearGroup.coe_scalar] at h
    rw [← h, smul_one_eq_diagonal]
    rfl
  have hone : M.map ⇑(1 : k ≃+* k) = M := by
    ext i j
    rfl
  have hM0 : M ≠ 0 := by
    intro h0
    have hu : IsUnit M.det := Matrix.isUnits_det_units A
    rw [h0, Matrix.det_zero] at hu
    exact not_isUnit_zero hu
  have hcfix : σ (c : k) = c := by
    have h1 : (M * M.map σ * M.map ⇑(σ * σ)).map σ = M.map σ * M.map ⇑(σ * σ) * M := by
      rw [map_mul_ringEquiv', map_mul_ringEquiv', map_map_ringEquiv' σ σ,
        map_map_ringEquiv' σ (σ * σ), ← mul_assoc σ σ σ, hσσσ, hone]
    rw [hN, map_smul_ringEquiv', map_one_ringEquiv'] at h1
    have h2 : M * (σ (c : k) • (1 : Matrix ι ι k)) = (c : k) • M := by
      rw [h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hN, Matrix.smul_mul, Matrix.one_mul]
    rw [Matrix.mul_smul, Matrix.mul_one] at h2
    have h3 : ((c : k)⁻¹ * σ (c : k)) • M = M := by
      rw [← smul_smul, h2, smul_smul, inv_mul_cancel₀ (Units.ne_zero c), one_smul]
    have h4 := eq_one_of_smul_eq_self' hM0 h3
    rw [inv_mul_eq_one₀ (Units.ne_zero c)] at h4
    exact h4.symm
  obtain ⟨d, hd⟩ := CFSG.ABGLocalTools.exists_prod_pow_eq σ hcfix
  rw [hσ] at hd
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, pow_zero, pow_one,
    pow_two, RingAut.one_apply, RingAut.mul_apply] at hd
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [zero_mul, zero_mul] at hd
    exact c.ne_zero hd.symm
  set A' : Matrix ι ι k := d⁻¹ • M with hA'
  have hA'unit : IsUnit A'.det := by
    rw [hA', Matrix.det_smul]
    exact (IsUnit.pow _ (isUnit_iff_ne_zero.mpr (inv_ne_zero hd0))).mul
      (Matrix.isUnits_det_units A)
  have hper : ∀ v : ι → k, (fun w : ι → k => A' *ᵥ (σ ∘ w))^[3] v = v := by
    intro v
    have hmv : ∀ (X : Matrix ι ι k) (w : ι → k), σ ∘ (X *ᵥ w) = X.map σ *ᵥ (σ ∘ w) :=
      fun X w => funext fun i => RingHom.map_mulVec (σ : k →+* k) X w i
    change A' *ᵥ (σ ∘ (A' *ᵥ (σ ∘ (A' *ᵥ (σ ∘ v))))) = v
    rw [hmv, hmv, hmv]
    simp only [Matrix.mulVec_mulVec]
    have hv : σ ∘ (σ ∘ (σ ∘ v)) = v := funext fun i => hσx (v i)
    have e1 : A' * (A'.map σ * (A'.map σ).map σ) =
        (d⁻¹ * σ d⁻¹ * σ (σ d⁻¹)) • (M * M.map σ * M.map ⇑(σ * σ)) := by
      rw [hA', map_smul_ringEquiv', map_smul_ringEquiv', map_map_ringEquiv' σ σ M]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
      congr 1
      ring
    have key : A' * (A'.map σ * (A'.map σ).map σ) = 1 := by
      rw [e1, hN, smul_smul, map_inv₀, map_inv₀, ← hd]
      rw [show d⁻¹ * (σ d)⁻¹ * (σ (σ d))⁻¹ * (d * σ d * σ (σ d)) = 1 by
        have h1 : σ d ≠ 0 := (map_ne_zero σ).mpr hd0
        have h2 : σ (σ d) ≠ 0 := (map_ne_zero σ).mpr h1
        field_simp, one_smul]
    rw [key, Matrix.one_mulVec]
    exact hv
  have : Fintype k := Fintype.ofFinite k
  obtain ⟨ℓ, -, e, hℓ, hcard⟩ := FiniteField.card' k
  obtain ⟨B, hB, hfix⟩ := exists_isUnit_det_fixed_index hℓ e.pos
    (by rw [Nat.card_eq_fintype_card, hcard]) σ hσ A' hA'unit hper
  refine ⟨((Matrix.isUnit_iff_isUnit_det B).mpr hB).unit, Units.mk0 d hd0, ?_⟩
  apply Units.ext
  rw [Units.val_mul, hmap, Units.val_mul, GeneralLinearGroup.coe_scalar, IsUnit.unit_spec,
    Units.val_mk0]
  have h5 : M * B.map σ = d • B := by
    have h6 := congrArg (fun X => d • X) hfix
    simp only [hA', Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hd0, one_smul] at h6
    exact h6
  rw [h5, smul_eq_diagonal_mul]
  rfl

end Index

section Symplectic

variable {r : ℕ} {K : Type} [Field K]

theorem dotProduct_formJ_mulVec_self (v : Fin r ⊕ Fin r → K) : v ⬝ᵥ (formJ r K *ᵥ v) = 0 := by
  simp only [formJ, dotProduct, Fintype.sum_sum_type, Matrix.mulVec, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add, add_zero, Matrix.neg_apply,
    neg_mul, Finset.sum_neg_distrib, Matrix.one_apply, ite_mul, one_mul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, mul_neg]
  rw [← sub_eq_add_neg, sub_eq_zero]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem formJ_map (σ : K ≃+* K) : (formJ r K).map σ = formJ r K := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [formJ, Matrix.one_apply]

theorem formJ_eq_neg_J : formJ r K = -Matrix.J (Fin r) K := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [formJ, Matrix.J]

theorem scalar_mem_gsp (c : Kˣ) : GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c ∈ gsp r K := by
  refine ⟨c * c, ?_⟩
  have h : ((GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = (c : K) • (1 : Matrix _ _ K) := by
    rw [GeneralLinearGroup.coe_scalar, smul_one_eq_diagonal]
    rfl
  rw [h, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul,
    Matrix.mul_smul, Matrix.mul_one, smul_smul, Units.val_mul]

theorem conjAut_scalar_eq_one (c : Kˣ) : conjAut r K ⟨_, scalar_mem_gsp c⟩ = 1 := by
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective x
  rw [conjAut_proj, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  rw [coe_conjSp]
  have hz : GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c ∈
      Subgroup.center (GL (Fin r ⊕ Fin r) K) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  change GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c * (g : GL (Fin r ⊕ Fin r) K) *
    (GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c)⁻¹ = g
  rw [← Subgroup.mem_center_iff.mp hz (g : GL (Fin r ⊕ Fin r) K), mul_inv_cancel_right]

theorem exists_eq_smul_one_of_forall {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {M : Matrix ι ι K} (h : ∀ v : ι → K, v ≠ 0 → ∃ a : K, a • (M *ᵥ v) = v) :
    ∃ c : K, M = c • (1 : Matrix ι ι K) := by
  classical
  have hmv : ∀ j i : ι, (M *ᵥ Pi.single j 1) i = M i j := fun j i => by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hoff : ∀ i j, i ≠ j → M i j = 0 := fun i j hij => by
    obtain ⟨a, ha⟩ := h (Pi.single j 1) (Pi.single_ne_zero_iff.mpr one_ne_zero)
    have h1 := congrFun ha j
    have h2 := congrFun ha i
    simp only [Pi.smul_apply, smul_eq_mul, hmv, Pi.single_eq_same,
      Pi.single_eq_of_ne hij] at h1 h2
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_mul] at h1
      exact zero_ne_one h1
    exact (mul_eq_zero.mp h2).resolve_left ha0
  have hdiag : ∀ i j, M i i = M j j := fun i j => by
    by_cases hij : i = j
    · rw [hij]
    have hv0 : (Pi.single i 1 + Pi.single j 1 : ι → K) ≠ 0 := by
      intro h0
      have := congrFun h0 i
      simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij, add_zero,
        Pi.zero_apply] at this
      exact one_ne_zero this
    obtain ⟨b, hb⟩ := h _ hv0
    have hi := congrFun hb i
    have hj := congrFun hb j
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec_add, Pi.add_apply, hmv,
      Pi.single_eq_same, Pi.single_eq_of_ne hij, Pi.single_eq_of_ne (Ne.symm hij), add_zero,
      zero_add] at hi hj
    rw [hoff i j hij, add_zero] at hi
    rw [hoff j i (Ne.symm hij), zero_add] at hj
    exact mul_left_cancel₀ (left_ne_zero_of_mul_eq_one hi) (hi.trans hj.symm)
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  refine ⟨M i₀ i₀, Matrix.ext fun i j => ?_⟩
  by_cases hij : i = j
  · subst hij
    simp [hdiag i i₀]
  · simp [hoff i j hij, hij]

theorem exists_scalar_of_conjAut_eq_one [Finite K] (hr : 1 ≤ r) {A : gsp r K}
    (hA : conjAut r K A = 1) :
    ∃ c : Kˣ, (A : GL (Fin r ⊕ Fin r) K) = GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c := by
  have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hA' : fieldAut r K 1 = conjAut r K A := by rw [hA, map_one]
  obtain ⟨c, hc⟩ := exists_eq_smul_one_of_forall (M := ((A : GL (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) fun v hv => by
    obtain ⟨a, ha⟩ := exists_smul_mulVec_eq_of_fieldAut_eq hr hA' hv
    exact ⟨a, ha⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    have hu : IsUnit ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).det :=
      Matrix.isUnits_det_units _
    rw [hc, zero_smul, Matrix.det_zero] at hu
    exact not_isUnit_zero hu
  refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
  rw [hc, GeneralLinearGroup.coe_scalar, Units.val_mk0, smul_one_eq_diagonal]
  rfl

theorem exists_gsp_mul_map_eq_scalar_mul [Finite K] (hr : 1 ≤ r) {σ : K ≃+* K}
    (hσ : orderOf σ = 3) (A : gsp r K) {c : Kˣ}
    (hc : GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c = (A : GL (Fin r ⊕ Fin r) K) *
      GeneralLinearGroup.map (σ : K →+* K) (A : GL (Fin r ⊕ Fin r) K) *
      GeneralLinearGroup.map ((σ * σ : K ≃+* K) : K →+* K) (A : GL (Fin r ⊕ Fin r) K)) :
    ∃ (H : gsp r K) (d : Kˣ), (A : GL (Fin r ⊕ Fin r) K) *
      GeneralLinearGroup.map (σ : K →+* K) (H : GL (Fin r ⊕ Fin r) K) =
        GeneralLinearGroup.scalar (Fin r ⊕ Fin r) d * H := by
  classical
  have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ, pow_orderOf_eq_one]
  have hσx : ∀ x, σ (σ (σ x)) = x := fun x => iterate_three_apply_of_pow hσ3 x
  obtain ⟨H₁, d₁, hH₁⟩ :=
    exists_mul_map_eq_scalar_mul_of_orderOf_eq_three_index hσ (A : GL (Fin r ⊕ Fin r) K) hc
  set J : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K := formJ r K with hJ
  set M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM
  set Mi : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    (((A : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hMi
  set X : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
    (H₁ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hX
  obtain ⟨μA, hμA⟩ := A.2
  have hMiM : Mi * M = 1 := by rw [hMi, hM, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hMiJ : Miᵀ * J * Mi = ((μA⁻¹ : Kˣ) : K) • J := inv_transpose_formJ hμA
  have hXσ : M * X.map σ = (d₁ : K) • X := by
    have h1 := congrArg (fun Y : GL (Fin r ⊕ Fin r) K =>
      (Y : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) hH₁
    simp only [Units.val_mul, GeneralLinearGroup.coe_scalar] at h1
    rw [smul_eq_diagonal_mul]
    exact h1
  have hXσ' : X.map σ = (d₁ : K) • (Mi * X) := by
    calc X.map σ = Mi * (M * X.map σ) := by rw [← Matrix.mul_assoc, hMiM, Matrix.one_mul]
      _ = _ := by rw [hXσ, Matrix.mul_smul]
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K, B = Xᵀ * J * X := ⟨_, rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : K, μ = (d₁ : K) * d₁ * ((μA⁻¹ : Kˣ) : K) := ⟨_, rfl⟩
  have hBσ : B.map σ = μ • B := by
    have e1 : (Xᵀ * J * X).map σ = (X.map σ)ᵀ * J * X.map σ := by
      rw [map_mul_ringEquiv', map_mul_ringEquiv', ← Matrix.transpose_map, hJ, formJ_map]
    have e2 : Xᵀ * Miᵀ * J * (Mi * X) = ((μA⁻¹ : Kˣ) : K) • (Xᵀ * J * X) := by
      calc Xᵀ * Miᵀ * J * (Mi * X) = Xᵀ * (Miᵀ * J * Mi) * X := by
            simp only [Matrix.mul_assoc]
        _ = ((μA⁻¹ : Kˣ) : K) • (Xᵀ * J * X) := by
            rw [hMiJ, Matrix.mul_smul, Matrix.smul_mul]
    rw [hB, e1, hXσ', Matrix.transpose_smul, Matrix.transpose_mul, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, e2, smul_smul, hμ]
  have hXdet : X.det ≠ 0 := (Matrix.isUnits_det_units H₁).ne_zero
  have hJdet : J.det ≠ 0 := by
    rw [hJ, formJ_eq_neg_J, Matrix.det_neg]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (Matrix.isUnit_det_J (Fin r) K).ne_zero
  have hBdet : B.det ≠ 0 := by
    rw [hB, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (mul_ne_zero hXdet hJdet) hXdet
  have hB0 : B ≠ 0 := by
    intro h0
    rw [h0, Matrix.det_zero] at hBdet
    exact hBdet rfl
  have hμ3 : μ * σ μ * σ (σ μ) = 1 := by
    have h1 : ((B.map σ).map σ).map σ = B := by
      ext i j
      simp [hσx]
    rw [hBσ, map_smul_ringEquiv', hBσ, smul_smul, map_smul_ringEquiv', hBσ, smul_smul] at h1
    have h2 := eq_one_of_smul_eq_self' hB0 h1
    rw [← h2, map_mul]
    ring
  have hμ0 : μ ≠ 0 := by
    rw [hμ]
    exact mul_ne_zero (mul_ne_zero d₁.ne_zero d₁.ne_zero) (Units.ne_zero _)
  let a : K ≃+ K :=
    { toFun := fun x => μ * σ x
      invFun := fun x => σ.symm (μ⁻¹ * x)
      left_inv := fun x => by
        simp only
        rw [inv_mul_cancel_left₀ hμ0, RingEquiv.symm_apply_apply]
      right_inv := fun x => by
        simp only
        rw [RingEquiv.apply_symm_apply, mul_inv_cancel_left₀ hμ0]
      map_add' := fun x y => by simp only [map_add, mul_add] }
  have ha : ∀ (c v : K), a (c • v) = σ c • a v := fun c v => by
    change μ * σ (c * v) = σ c * (μ * σ v)
    rw [map_mul]
    ring
  have hah : ∀ v, (⇑a)^[3] v = v := fun v => by
    change μ * σ (μ * σ (μ * σ v)) = v
    rw [map_mul, map_mul, map_mul, hσx]
    calc μ * (σ μ * (σ (σ μ) * v)) = (μ * σ μ * σ (σ μ)) * v := by ring
      _ = v := by rw [hμ3, one_mul]
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨ℓ, -, e, hℓ, hcard⟩ := FiniteField.card' K
  obtain ⟨-, k₀, hk₀, -, bt, hbt, -⟩ :=
    CFSG.RankThree.Classical.semilinear_fixed_basis hℓ e.pos
      (by rw [Nat.card_eq_fintype_card, hcard]) σ hσ (Module.finrank_self K) a ha hah
  have ht0 : bt 0 ≠ 0 := bt.ne_zero 0
  have hμt : μ * σ (bt 0) = bt 0 := hbt 0
  obtain ⟨B', hB'⟩ : ∃ B' : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K, B' = bt 0 • B :=
    ⟨_, rfl⟩
  have hB'σ : B'.map σ = B' := by
    rw [hB', map_smul_ringEquiv', hBσ, smul_smul,
      show σ (bt 0) * μ = bt 0 by rw [mul_comm]; exact hμt]
  have hk₀mem : ∀ x, x ∈ k₀ ↔ σ x = x := fun x => by
    rw [← SetLike.mem_coe, hk₀]
    rfl
  have hB'mem : ∀ i j, B' i j ∈ k₀ := fun i j =>
    (hk₀mem _).mpr (congrFun (congrFun hB'σ i) j)
  let B₀ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k₀ := fun i j => ⟨B' i j, hB'mem i j⟩
  have hB₀map : B₀.map k₀.subtype = B' := by
    ext i j
    rfl
  have hB'det : B'.det ≠ 0 := by
    rw [hB', Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ ht0) hBdet
  have hB₀det : B₀.det ≠ 0 := by
    intro h0
    apply hB'det
    rw [← hB₀map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  have halt : (Matrix.toBilin' B₀).IsAlt := by
    intro x
    rw [Matrix.toBilin'_apply']
    apply k₀.subtype_injective
    rw [map_zero]
    have e3 : k₀.subtype (x ⬝ᵥ B₀ *ᵥ x) =
        (fun i => (x i : K)) ⬝ᵥ (B' *ᵥ fun i => (x i : K)) := by
      rw [← hB₀map]
      simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, Matrix.map_apply]
      rfl
    rw [e3, hB', Matrix.smul_mulVec, dotProduct_smul, hB, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hJ,
      dotProduct_formJ_mulVec_self, smul_zero]
  have hnd : (Matrix.toBilin' B₀).Nondegenerate :=
    LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' B₀ hB₀det
  obtain ⟨m, bJ, hbJ⟩ := LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J halt hnd
  have hm : m = r := by
    have h1 := Module.finrank_eq_card_basis bJ
    rw [Module.finrank_fintype_fun_eq_card] at h1
    simp only [Fintype.card_sum, Fintype.card_fin] at h1
    omega
  subst m
  set P₀ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) k₀ :=
    (Pi.basisFun k₀ (Fin r ⊕ Fin r)).toMatrix bJ with hP₀def
  have hP₀ : P₀ᵀ * B₀ * P₀ = Matrix.J (Fin r) k₀ := by
    have h1 := LinearMap.BilinForm.toMatrix_mul_basis_toMatrix
      (Pi.basisFun k₀ (Fin r ⊕ Fin r)) bJ (Matrix.toBilin' B₀)
    rw [LinearMap.BilinForm.toMatrix_basisFun, LinearMap.BilinForm.toMatrix'_toBilin', hbJ] at h1
    exact h1
  have hP₀det : IsUnit P₀.det := by
    rw [hP₀def, ← Module.Basis.det_apply]
    exact (Pi.basisFun k₀ (Fin r ⊕ Fin r)).isUnit_det bJ
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K, P = P₀.map k₀.subtype :=
    ⟨_, rfl⟩
  have hPσ : P.map σ = P := by
    rw [hP]
    ext i j
    exact (hk₀mem _).mp (P₀ i j).2
  have hPJ : Pᵀ * B' * P = Matrix.J (Fin r) K := by
    have h1 := congrArg k₀.subtype.mapMatrix hP₀
    rw [map_mul, map_mul, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
      RingHom.mapMatrix_apply, Matrix.transpose_map, hB₀map, ← hP] at h1
    rw [h1]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.J, Matrix.one_apply] <;>
      split_ifs <;> simp
  set Hgl : GL (Fin r ⊕ Fin r) K := H₁ *
    Matrix.GeneralLinearGroup.map k₀.subtype ((Matrix.isUnit_iff_isUnit_det P₀).mpr hP₀det).unit
    with hHgl
  have hHmat : (Hgl : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = X * P := by
    rw [hHgl, Units.val_mul, hP]
    rfl
  have hmu0 : (-(bt 0)⁻¹ : K) ≠ 0 := neg_ne_zero.mpr (inv_ne_zero ht0)
  have hHgsp : Hgl ∈ gsp r K := by
    refine ⟨Units.mk0 _ hmu0, ?_⟩
    rw [hHmat, Units.val_mk0, Matrix.transpose_mul]
    calc Pᵀ * Xᵀ * formJ r K * (X * P) = Pᵀ * B * P := by
          rw [hB, hJ]
          simp only [Matrix.mul_assoc]
      _ = (bt 0)⁻¹ • (Pᵀ * B' * P) := by
          rw [hB', Matrix.mul_smul, Matrix.smul_mul, smul_smul, inv_mul_cancel₀ ht0, one_smul]
      _ = (-(bt 0)⁻¹) • formJ r K := by
          rw [hPJ, formJ_eq_neg_J, smul_neg, neg_smul, neg_neg]
  refine ⟨⟨Hgl, hHgsp⟩, d₁, ?_⟩
  apply Units.ext
  change M * ((Hgl : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map σ) =
    Matrix.scalar (Fin r ⊕ Fin r) (d₁ : K) * (Hgl : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
  rw [hHmat, map_mul_ringEquiv', hPσ, ← Matrix.mul_assoc, hXσ, Matrix.scalar_apply,
    ← smul_eq_diagonal_mul, Matrix.smul_mul]

end Symplectic

section Descent

variable {r : ℕ} {K : Type} [Field K]

theorem conjAut_mul_fieldAut_of_pow_three_eq_one [Finite K] (hr : 1 ≤ r) (A : gsp r K)
    (σ : K ≃+* K) (hσ1 : σ ≠ 1) (hα : (conjAut r K A * fieldAut r K σ) ^ 3 = 1) :
    orderOf σ = 3 ∧ ∃ H : gsp r K,
      conjAut r K A * fieldAut r K σ = conjAut r K H * fieldAut r K σ * (conjAut r K H)⁻¹ := by
  have h3 : conjAut r K (A * gspFieldMap σ A * gspFieldMap (σ * σ) A) *
      fieldAut r K (σ * σ * σ) = 1 := by
    rw [← conjAut_mul_fieldAut_mul, ← conjAut_mul_fieldAut_mul, ← hα, pow_three']
  have hf : fieldAut r K (σ * σ * σ) ∈ (conjAut r K).range :=
    ⟨(A * gspFieldMap σ A * gspFieldMap (σ * σ) A)⁻¹, by
      rw [map_inv]
      exact (eq_inv_of_mul_eq_one_right h3).symm⟩
  have hσσσ := (fieldAut_mem_range_conjAut_iff hr).mp hf
  have hσ3 : orderOf σ = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime (by rw [pow_three', hσσσ]) hσ1
  rw [hσσσ, map_one, mul_one] at h3
  obtain ⟨c, hc⟩ := exists_scalar_of_conjAut_eq_one hr h3
  have hc' : GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c = (A : GL (Fin r ⊕ Fin r) K) *
      GeneralLinearGroup.map (σ : K →+* K) (A : GL (Fin r ⊕ Fin r) K) *
      GeneralLinearGroup.map ((σ * σ : K ≃+* K) : K →+* K) (A : GL (Fin r ⊕ Fin r) K) := by
    rw [← hc]
    rfl
  obtain ⟨H, d, hH⟩ := exists_gsp_mul_map_eq_scalar_mul hr hσ3 A hc'
  refine ⟨hσ3, H, ?_⟩
  have hAeq : A = ⟨_, scalar_mem_gsp d⟩ * H * (gspFieldMap σ H)⁻¹ :=
    Subtype.ext (eq_mul_inv_of_mul_eq hH)
  rw [hAeq, map_mul, map_mul, map_inv, conjAut_scalar_eq_one, one_mul,
    ← fieldAut_mul_conjAut_mul_inv σ H]
  group

theorem symplectic_order_three_field_descent [Finite K] (hr : 3 ≤ r)
    (α : MulAut (StatedProj (StatedSp r K))) (hα : α ^ 3 = 1)
    (hD : α ∉ (conjAut r K).range) :
    ∃ σ : K ≃+* K, orderOf σ = 3 ∧ ∃ H : gsp r K,
      α = conjAut r K H * fieldAut r K σ * (conjAut r K H)⁻¹ := by
  obtain ⟨-, hform⟩ := automorphism_generation (K := K) hr
  obtain ⟨A, σ, rfl⟩ := hform α
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [map_one, mul_one] at hD
    exact hD ⟨A, rfl⟩
  obtain ⟨h3, H, hH⟩ := conjAut_mul_fieldAut_of_pow_three_eq_one (by omega) A σ hσ1 hα
  exact ⟨σ, h3, H, hH⟩

theorem sp4_even_order_three_field_descent {F : Type} [Field F] [Finite F] [CharP F 2]
    (α : MulAut (StatedProj (StatedSp 2 F))) (hα : α ^ 3 = 1)
    (hD : α ∉ (conjAut 2 F).range) :
    ∃ σ : F ≃+* F, orderOf σ = 3 ∧ ∃ H : gsp 2 F,
      α = conjAut 2 F H * fieldAut 2 F σ * (conjAut 2 F H)⁻¹ := by
  obtain ⟨A, σ, ε, hε, rfl⟩ := exists_eq_conjAut_mul_fieldAut_mul_tauAut_pow α
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · rw [pow_zero, mul_one] at hα hD ⊢
    have hσ1 : σ ≠ 1 := by
      rintro rfl
      rw [map_one, mul_one] at hD
      exact hD ⟨A, rfl⟩
    obtain ⟨h3, H, hH⟩ := conjAut_mul_fieldAut_of_pow_three_eq_one (by norm_num) A σ hσ1 hα
    exact ⟨σ, h3, H, hH⟩
  · exfalso
    obtain ⟨-, -, -, hindex⟩ :=
      CFSG.ComponentClassification.CatalogueBSymplecticTwo.kernel_generation (K := F)
    have hτ : (CFSG.QuasithinUnique.Lin2.Five.tauAut : MulAut (StatedProj (StatedSp 2 F))) ∉
        spSemilinearAutGroup 2 F := CFSG.QuasithinUnique.Lin2.Five.tauAut_not_mem_E
    have hidx : (spSemilinearAutGroup 2 F).index = 2 := by
      have h1 : (spSemilinearAutGroup 2 F).index ≠ 1 := by
        rw [Ne, Subgroup.index_eq_one]
        intro htop
        exact hτ (htop ▸ Subgroup.mem_top _)
      have h0 : (spSemilinearAutGroup 2 F).index ≠ 0 := Subgroup.index_ne_zero_of_finite
      omega
    have heE : conjAut 2 F A * fieldAut 2 F σ ∈ spSemilinearAutGroup 2 F :=
      mem_spSemilinearAutGroup_iff.mpr ⟨A, σ, rfl⟩
    have hβ : conjAut 2 F A * fieldAut 2 F σ * CFSG.QuasithinUnique.Lin2.Five.tauAut ^ 1 ∉
        spSemilinearAutGroup 2 F := by
      intro hmem
      apply hτ
      have h1 := mul_mem (inv_mem heE) hmem
      rwa [pow_one, ← mul_assoc, inv_mul_cancel, one_mul] at h1
    have h2 := Subgroup.mul_self_mem_of_index_two hidx
      (conjAut 2 F A * fieldAut 2 F σ * CFSG.QuasithinUnique.Lin2.Five.tauAut ^ 1)
    have h3 : (conjAut 2 F A * fieldAut 2 F σ * CFSG.QuasithinUnique.Lin2.Five.tauAut ^ 1) ^ 3 ∈
        spSemilinearAutGroup 2 F := by
      rw [hα]
      exact one_mem _
    rw [pow_three', Subgroup.mul_mem_iff_of_index_two hidx] at h3
    exact hβ (h3.mp h2)

theorem isField_psp_of_pow_three_eq_one [Finite K] (hr : 3 ≤ r)
    {α : MulAut (StatedProj (StatedSp r K))} (hα : α ^ 3 = 1)
    (hD : α ∉ (conjAut r K).range) : (stdPinnedPSp r K).IsField α := by
  obtain ⟨σ, hσ, H, rfl⟩ := symplectic_order_three_field_descent hr α hα hD
  refine ⟨fieldAut r K σ, ⟨σ, rfl⟩, fun h1 => ?_, conjAut r K H, ⟨H, rfl⟩, rfl⟩
  have h2 := (fieldAut_mem_range_conjAut_iff (r := r) (K := K) (by omega)).mp
    (by rw [h1]; exact one_mem _)
  rw [h2, orderOf_one] at hσ
  omega

theorem isField_psp4Even_of_pow_three_eq_one {F : Type} [Field F] [Finite F] [CharP F 2]
    {α : MulAut (StatedProj (StatedSp 2 F))} (hα : α ^ 3 = 1)
    (hD : α ∉ (conjAut 2 F).range) : (stdPinnedPSp4Even F).IsField α := by
  obtain ⟨σ, hσ, H, rfl⟩ := sp4_even_order_three_field_descent α hα hD
  refine ⟨fieldAut 2 F σ, ⟨σ, rfl⟩, fun h1 => ?_, conjAut 2 F H, ⟨H, rfl⟩, rfl⟩
  have h2 := (fieldAut_mem_range_conjAut_iff (r := 2) (K := F) (by norm_num)).mp
    (by rw [h1]; exact one_mem _)
  rw [h2, orderOf_one] at hσ
  omega

end Descent

section Induced

variable {G : Type*} [Group G] [Finite G] (L : Subgroup G)

theorem inducesKindPSp_diagonal_or_field {r : ℕ} {K : Type} [Field K] [Finite K] (hr : 3 ≤ r)
    {x : G} (hx3 : x ^ 3 = 1) (hout : InducesOuterTheta x L)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* StatedProj (StatedSp r K)) :
    InducesKind L (stdPinnedPSp r K) e x .diagonal ∨
      InducesKind L (stdPinnedPSp r K) e x .field := by
  obtain ⟨hx, -⟩ := id hout
  have hnot := (not_isInnerAut_inducedAutHom_iff L e hx).mpr hout
  by_cases hD : inducedAutHom L e ⟨x, hx⟩ ∈ (conjAut r K).range
  · exact Or.inl ⟨hx, hD, hnot⟩
  · exact Or.inr ⟨hx, isField_psp_of_pow_three_eq_one hr (inducedAutHom_pow_eq_one L e hx hx3) hD⟩

theorem inducesKindPSp4Even_diagonal_or_field {F : Type} [Field F] [Finite F] [CharP F 2]
    {x : G} (hx3 : x ^ 3 = 1) (hout : InducesOuterTheta x L)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* StatedProj (StatedSp 2 F)) :
    InducesKind L (stdPinnedPSp4Even F) e x .diagonal ∨
      InducesKind L (stdPinnedPSp4Even F) e x .field := by
  obtain ⟨hx, -⟩ := id hout
  have hnot := (not_isInnerAut_inducedAutHom_iff L e hx).mpr hout
  by_cases hD : inducedAutHom L e ⟨x, hx⟩ ∈ (conjAut 2 F).range
  · exact Or.inl ⟨hx, hD, hnot⟩
  · exact Or.inr ⟨hx, isField_psp4Even_of_pow_three_eq_one
      (inducedAutHom_pow_eq_one L e hx hx3) hD⟩

end Induced

end CFSG.RankThree.PartTwo.KFacts
