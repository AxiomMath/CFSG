module

public import CFSG.RankThree.PartTwo.KFacts.AutPSL
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution
import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneLinearField
import CFSG.RankThree.Classical2.MatrixFrobeniusLang
import CFSG.GroupTheory.ABGLocalTools.SL2FieldAutSemilinear

public section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix

variable {K : Type*} [Field K] {n : ℕ}

theorem iterate_three_apply_of_pow {σ : K ≃+* K} (hσ : σ ^ 3 = 1) (x : K) :
    (⇑σ)^[3] x = x := by
  have h := congrArg (fun τ : K ≃+* K => τ x) hσ
  simp only [pow_succ, pow_zero, one_mul, RingAut.mul_apply, RingAut.one_apply] at h
  exact h

theorem eq_frobenius_pow_of_orderOf_eq_three {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = p ^ f) {σ : K ≃+* K} (hσ : orderOf σ = 3) :
    3 ∣ f ∧ ((∀ x, σ x = x ^ p ^ (f / 3)) ∨ ∀ x, σ x = x ^ p ^ (2 * f / 3)) := by
  obtain ⟨φ, hφ, hord, hzp, -⟩ := finite_field_automorphism_fixed_field_cardinality hp hf hK
  have hφfin : IsOfFinOrder φ := orderOf_pos_iff.mp (by rw [hord]; omega)
  obtain ⟨k, hk, rfl⟩ : ∃ k < f, φ ^ k = σ := by
    have hmem : σ ∈ Subgroup.zpowers φ := hzp ▸ Subgroup.mem_top σ
    rw [← hφfin.mem_powers_iff_mem_zpowers] at hmem
    obtain ⟨k, hk⟩ := hmem
    refine ⟨k % f, Nat.mod_lt _ (by omega), ?_⟩
    rw [← hk, ← hord, pow_mod_orderOf]
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_one] at hσ
    omega
  have h3k : f ∣ 3 * k := by
    rw [← hord, orderOf_dvd_iff_pow_eq_one, mul_comm, pow_mul, ← hσ, pow_orderOf_eq_one]
  obtain ⟨c, hc⟩ := h3k
  have hc12 : c = 1 ∨ c = 2 := by
    rcases c with _ | _ | _ | c
    · omega
    · exact Or.inl rfl
    · exact Or.inr rfl
    · nlinarith
  have hpow : ∀ (j : ℕ) (x : K), (φ ^ j) x = x ^ p ^ j := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
      intro x
      rw [pow_succ, RingAut.mul_apply, hφ, ih, ← pow_mul, pow_succ, mul_comm]
  rcases hc12 with rfl | rfl
  · refine ⟨⟨k, by omega⟩, Or.inl fun x => ?_⟩
    rw [hpow, show f / 3 = k by omega]
  · refine ⟨⟨f / 3, by omega⟩, Or.inr fun x => ?_⟩
    rw [hpow, show 2 * f / 3 = k by omega]

theorem map_map_ringAut (σ τ : K ≃+* K) (M : Matrix (Fin n) (Fin n) K) :
    (M.map τ).map σ = M.map ⇑(σ * τ) := by
  rw [Matrix.map_map]
  rfl

theorem map_mul_ringAut (σ : K ≃+* K) (X Y : Matrix (Fin n) (Fin n) K) :
    (X * Y).map σ = X.map σ * Y.map σ :=
  Matrix.map_mul (f := (σ : K →+* K))

theorem map_smul_ringAut (σ : K ≃+* K) (a : K) (X : Matrix (Fin n) (Fin n) K) :
    (a • X).map σ = σ a • X.map σ := by
  ext i j
  simp

theorem map_one_ringAut (σ : K ≃+* K) : (1 : Matrix (Fin n) (Fin n) K).map σ = 1 :=
  Matrix.map_one _ (map_zero σ) (map_one σ)

theorem exists_mul_map_eq_scalar_mul_of_orderOf_eq_three [Finite K] (hn : 1 ≤ n)
    {σ : K ≃+* K} (hσ : orderOf σ = 3) (A : GL (Fin n) K) {c : Kˣ}
    (hc : GeneralLinearGroup.scalar (Fin n) c = A * GeneralLinearGroup.map (σ : K →+* K) A *
      GeneralLinearGroup.map ((σ * σ : K ≃+* K) : K →+* K) A) :
    ∃ (H : GL (Fin n) K) (d : Kˣ), A * GeneralLinearGroup.map (σ : K →+* K) H =
      GeneralLinearGroup.scalar (Fin n) d * H := by
  classical
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ, pow_orderOf_eq_one]
  have hσσσ : σ * σ * σ = 1 := by rw [← hσ3, pow_succ, pow_two]
  set M : Matrix (Fin n) (Fin n) K := (A : Matrix (Fin n) (Fin n) K) with hM
  have hmap : ∀ (τ : K ≃+* K) (X : GL (Fin n) K),
      ((GeneralLinearGroup.map (τ : K →+* K) X : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (X : Matrix (Fin n) (Fin n) K).map τ := fun _ _ => rfl
  have hN : M * M.map σ * M.map ⇑(σ * σ) = (c : K) • (1 : Matrix (Fin n) (Fin n) K) := by
    have h := congrArg (fun X : GL (Fin n) K => (X : Matrix (Fin n) (Fin n) K)) hc
    simp only [Units.val_mul, hmap, GeneralLinearGroup.coe_scalar] at h
    rw [← h, smul_one_eq_diagonal]
    rfl
  have hcfix : σ (c : K) = c := by
    have hone : M.map ⇑(1 : K ≃+* K) = M := by
      ext i j
      rfl
    have h1 : (M * M.map σ * M.map ⇑(σ * σ)).map σ = M.map σ * M.map ⇑(σ * σ) * M := by
      rw [map_mul_ringAut, map_mul_ringAut, map_map_ringAut σ σ, map_map_ringAut σ (σ * σ),
        ← mul_assoc σ σ σ, hσσσ, hone]
    rw [hN, map_smul_ringAut, map_one_ringAut] at h1
    have h2 : M * (σ (c : K) • (1 : Matrix (Fin n) (Fin n) K)) = (c : K) • M := by
      rw [h1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hN, Matrix.smul_mul, Matrix.one_mul]
    rw [Matrix.mul_smul, Matrix.mul_one] at h2
    have hM0 : M ≠ 0 := by
      intro h0
      have hu : IsUnit M.det := Matrix.isUnits_det_units A
      have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
      rw [h0, Matrix.det_zero] at hu
      exact not_isUnit_zero hu
    obtain ⟨i, j, hij⟩ : ∃ i j, M i j ≠ 0 := by
      by_contra hall
      exact hM0 (Matrix.ext fun i j => by
        by_contra h
        exact hall ⟨i, j, h⟩)
    have h4 := congrFun (congrFun h2 i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at h4
    exact mul_right_cancel₀ hij h4
  obtain ⟨d, hd⟩ := CFSG.ABGLocalTools.exists_prod_pow_eq σ hcfix
  rw [hσ] at hd
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, pow_zero, pow_one,
    pow_two, RingAut.one_apply, RingAut.mul_apply] at hd
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [zero_mul, zero_mul] at hd
    exact c.ne_zero hd.symm
  set A' : Matrix (Fin n) (Fin n) K := d⁻¹ • M with hA'
  have hP : CFSG.RankThree.Classical2.twistedProd σ A' 3 = 1 := by
    change CFSG.RankThree.Classical2.twistedProd ((σ : K →+* K) : K → K) A' 3 = 1
    rw [CFSG.RankThree.Classical2.twistedProd_succ, CFSG.RankThree.Classical2.twistedProd_succ,
      CFSG.RankThree.Classical2.twistedProd_succ, CFSG.RankThree.Classical2.twistedProd_zero]
    change A' * (A' * (A' * (1 : Matrix (Fin n) (Fin n) K).map σ).map σ).map σ = 1
    have key : A' * (A' * (A' * (1 : Matrix (Fin n) (Fin n) K).map σ).map σ).map σ =
        (d⁻¹ * (σ d⁻¹ * σ (σ d⁻¹))) • (M * (M.map σ * M.map ⇑(σ * σ))) := by
      rw [map_one_ringAut, Matrix.mul_one, map_mul_ringAut, hA', map_smul_ringAut,
        map_smul_ringAut, map_map_ringAut σ σ M]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_assoc]
      congr 1
      ring
    rw [key, ← Matrix.mul_assoc, hN, smul_smul, map_inv₀, map_inv₀, ← hd]
    rw [show (d⁻¹ * ((σ d)⁻¹ * (σ (σ d))⁻¹)) * (d * σ d * σ (σ d)) = 1 by
      have h1 : σ d ≠ 0 := (map_ne_zero σ).mpr hd0
      have h2 : σ (σ d) ≠ 0 := (map_ne_zero σ).mpr h1
      field_simp, one_smul]
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨ℓ, -, e, hℓ, hcard⟩ := FiniteField.card' K
  have hA'unit : IsUnit A'.det := by
    rw [hA', Matrix.det_smul]
    exact (IsUnit.pow _ (isUnit_iff_ne_zero.mpr (inv_ne_zero hd0))).mul
      (Matrix.isUnits_det_units A)
  obtain ⟨B, hB, hfix⟩ := CFSG.RankThree.Classical2.exists_isUnit_det_fixed (n := n) hℓ e.pos
    (by rw [Nat.card_eq_fintype_card, hcard]) σ hσ A' hA'unit fun v => by
      rw [hP, Matrix.one_mulVec]
      funext i
      exact iterate_three_apply_of_pow hσ3 (v i)
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

theorem conjAut_mul_fieldAut_eq_conj (A H : GL (Fin n) K) (σ : K ≃+* K) (d : Kˣ)
    (h : A * GeneralLinearGroup.map (σ : K →+* K) H = GeneralLinearGroup.scalar (Fin n) d * H) :
    conjAut n K A * fieldAut n K σ = conjAut n K H * fieldAut n K σ * (conjAut n K H)⁻¹ := by
  have hA : A = GeneralLinearGroup.scalar (Fin n) d * H *
      (GeneralLinearGroup.map (σ : K →+* K) H)⁻¹ := by
    rw [← h]
    group
  have hfc := fieldAut_mul_conjAut (n := n) σ H⁻¹
  rw [hA, map_mul, map_mul, conjAut_scalar, one_mul, map_inv, ← map_inv]
  calc conjAut n K H * conjAut n K (GeneralLinearGroup.map (σ : K →+* K) H⁻¹) * fieldAut n K σ =
      conjAut n K H * (fieldAut n K σ * conjAut n K H⁻¹) := by rw [hfc]; group
    _ = conjAut n K H * fieldAut n K σ * (conjAut n K H)⁻¹ := by rw [map_inv]; group

theorem linear_order_three_field_descent [Finite K] (hn : 3 ≤ n) (α : MulAut (projectiveSL n K))
    (hα : α ^ 3 = 1) (hD : α ∉ linearAutGroup n K) :
    ∃ σ : K ≃+* K, orderOf σ = 3 ∧ ∃ H : GL (Fin n) K,
      α = conjAut n K H * fieldAut n K σ * (conjAut n K H)⁻¹ := by
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation (K := K) hn).2 α
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · rw [pow_zero, mul_one] at hα hD ⊢
    have hσ1 : σ ≠ 1 := by
      rintro rfl
      rw [map_one, mul_one] at hD
      exact hD (conjAut_mem_linearAutGroup A)
    have h3 : conjAut n K (A * GeneralLinearGroup.map (σ : K →+* K) A *
        GeneralLinearGroup.map ((σ * σ : K ≃+* K) : K →+* K) A) * fieldAut n K (σ * σ * σ) = 1 := by
      rw [← conjAut_mul_fieldAut_mul, ← conjAut_mul_fieldAut_mul, ← hα, pow_three']
    obtain ⟨hσσσ, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn _ _ h3
    have hσ3 : orderOf σ = 3 := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact orderOf_eq_prime (by rw [pow_three', hσσσ]) hσ1
    obtain ⟨H, d, hH⟩ :=
      exists_mul_map_eq_scalar_mul_of_orderOf_eq_three (by omega) hσ3 A hc
    exact ⟨σ, hσ3, H, conjAut_mul_fieldAut_eq_conj A H σ d hH⟩
  · exfalso
    rw [pow_one] at hα
    set e := conjAut n K A * fieldAut n K σ with he
    have heE : e ∈ semilinearAutGroup n K := mem_semilinearAutGroup_iff.mpr ⟨A, σ, rfl⟩
    have hδδ : dualAut n K * dualAut n K = 1 :=
      (standard_automorphism_transport (K := K) (n := n)).2.2.2.1
    have hx : e * (dualAut n K * e * dualAut n K) * e ∈ semilinearAutGroup n K :=
      mul_mem (mul_mem heE (dualAut_mul_mul_dualAut_mem heE)) heE
    have h3 : (e * dualAut n K) ^ 3 =
        e * (dualAut n K * e * dualAut n K) * e * dualAut n K := by
      rw [pow_three']
      group
    rw [h3] at hα
    have hδ : dualAut n K = (e * (dualAut n K * e * dualAut n K) * e)⁻¹ := by
      rw [← mul_eq_one_iff_eq_inv', hα]
    exact CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane.dualAut_not_mem_semilinearAutGroup
      (K := K) hn (hδ ▸ inv_mem hx)

theorem isField_of_pow_three_eq_one [Finite K] (hn : 3 ≤ n) {α : MulAut (projectiveSL n K)}
    (hα : α ^ 3 = 1) (hD : α ∉ linearAutGroup n K) : (stdPinnedPSL n K).IsField α := by
  obtain ⟨σ, hσ, H, rfl⟩ := linear_order_three_field_descent hn α hα hD
  refine ⟨fieldAut n K σ, ⟨σ, rfl⟩, fun h1 => ?_, conjAut n K H, conjAut_mem_linearAutGroup H,
    rfl⟩
  have h := (eq_one_of_conjAut_mul_fieldAut_eq_one hn 1 σ (by rw [map_one, one_mul, h1])).1
  rw [h, orderOf_one] at hσ
  omega

theorem hasKind_diagonal_or_field_of_pow_three_eq_one [Finite K] (hn : 3 ≤ n)
    {α : MulAut (projectiveSL n K)} (hα : α ^ 3 = 1) (hout : ¬ IsInnerAut α) :
    (stdPinnedPSL n K).HasKind α .diagonal ∨ (stdPinnedPSL n K).HasKind α .field := by
  by_cases hD : α ∈ linearAutGroup n K
  · exact Or.inl ⟨hD, hout⟩
  · exact Or.inr (isField_of_pow_three_eq_one hn hα hD)

section Induced

variable {G : Type*} [Group G] [Finite G] (L : Subgroup G) {M : Type*} [Group M]

theorem inducesKindPSL_diagonal_or_field [Finite K] (hn : 3 ≤ n) {x : G} (hx3 : x ^ 3 = 1)
    (hout : InducesOuterTheta x L)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* projectiveSL n K) :
    InducesKind L (stdPinnedPSL n K) e x .diagonal ∨
      InducesKind L (stdPinnedPSL n K) e x .field := by
  obtain ⟨hx, -⟩ := id hout
  rcases hasKind_diagonal_or_field_of_pow_three_eq_one hn (inducedAutHom_pow_eq_one L e hx hx3)
    ((not_isInnerAut_inducedAutHom_iff L e hx).mpr hout) with h | h
  · exact Or.inl ⟨hx, h⟩
  · exact Or.inr ⟨hx, h⟩

theorem inducesKindSL_inner_or_diagonal_or_field [Finite K] (hn : 3 ≤ n) {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G)) (hx3 : x ^ 3 = 1)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* SpecialLinearGroup (Fin n) K) :
    (stdPinnedPSL n K).HasKind (descendAut n K (inducedAutHom L e ⟨x, hx⟩)) .inner ∨
      (stdPinnedPSL n K).HasKind (descendAut n K (inducedAutHom L e ⟨x, hx⟩)) .diagonal ∨
      (stdPinnedPSL n K).HasKind (descendAut n K (inducedAutHom L e ⟨x, hx⟩)) .field := by
  by_cases hin : IsInnerAut (descendAut n K (inducedAutHom L e ⟨x, hx⟩))
  · exact Or.inl hin
  · refine Or.inr (hasKind_diagonal_or_field_of_pow_three_eq_one hn ?_ hin)
    rw [← map_pow, inducedAutHom_pow_eq_one L e hx hx3, map_one]

end Induced

end CFSG.RankThree.PartTwo.KFacts
