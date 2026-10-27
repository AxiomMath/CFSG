module

public import CFSG.RankThree.PartTwo.KFacts.AS76Tools
public import CFSG.RankThree.PartTwo.KFacts.KS21AutThreeL44
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofSquareZero

public noncomputable section

namespace CFSG.RankThree.PartTwo.Sec21.AS76.L44

open CFSG.RankThree.PartTwo.Sec21.AS76

open Module Matrix CFSG.LieType.BorelTits CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem exists_matrixUnits_of_sq_eq_zero {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hV : 4 ≤ finrank K V) (N : Module.End K V) (hN : N * N = 0) :
    ∃ X X' : Module.End K V, X * X = 0 ∧ X' * X' = 0 ∧ X * X' * X = X ∧ X' * X * X' = X' ∧
      X * N = N * X ∧ X' * N = N * X' ∧ X ≠ 0 := by
  classical
  obtain ⟨r, b, hb1, hb2⟩ := CFSG.ComponentClassification.RankTwoClassical.exists_basis_sq_eq_zero
    N (by rw [← Module.End.mul_eq_comp]; exact hN)
  have hcard := Module.finrank_eq_card_basis b
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at hcard
  generalize finrank K (LinearMap.range N) = ℓ at b hb1 hb2 hcard
  by_cases hr : 2 ≤ r
  · set k₀ : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) := .inr (.inr ⟨0, by omega⟩) with hk₀
    set k₁ : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) := .inr (.inr ⟨1, by omega⟩) with hk₁
    have h01 : k₀ ≠ k₁ := by simp [k₀, k₁]
    have hcomm : ∀ j j' : Fin r, bE b (.inr (.inr j)) (.inr (.inr j')) * N =
        N * bE b (.inr (.inr j)) (.inr (.inr j')) := by
      intro j j'
      apply b.ext
      intro k
      rw [Module.End.mul_apply, Module.End.mul_apply]
      rcases k with i | k
      · rw [hb1, bE_basis, bE_basis, ite_eq_right (by simp), ite_eq_right (by simp), map_zero]
      · rw [hb2, map_zero, bE_basis]
        split_ifs
        · rw [hb2]
        · rw [map_zero]
    refine ⟨bE b k₀ k₁, bE b k₁ k₀, ?_, ?_, ?_, ?_, hcomm _ _, hcomm _ _, ?_⟩
    · rw [bE_mul_bE, ite_eq_right h01]
    · rw [bE_mul_bE, ite_eq_right h01.symm]
    · rw [bE_mul_bE, ite_eq_left rfl, bE_mul_bE, ite_eq_left rfl]
    · rw [bE_mul_bE, ite_eq_left rfl, bE_mul_bE, ite_eq_left rfl]
    · intro h0
      have h1 := congrArg (fun T : Module.End K V => T (b k₁)) h0
      simp only [bE_basis, LinearMap.zero_apply] at h1
      exact b.ne_zero k₀ h1
  · have hℓ2 : 2 ≤ ℓ := by omega
    set i₀ : Fin ℓ := ⟨0, by omega⟩ with hi₀
    set i₁ : Fin ℓ := ⟨1, by omega⟩ with hi₁
    have hi : i₀ ≠ i₁ := by simp [i₀, i₁]
    set X := bE b (.inl i₀) (.inl i₁) + bE b (.inr (.inl i₀)) (.inr (.inl i₁)) with hX
    set X' := bE b (.inl i₁) (.inl i₀) + bE b (.inr (.inl i₁)) (.inr (.inl i₀)) with hX'
    have hcomm : ∀ i i' : Fin ℓ, i ≠ i' →
        (bE b (.inl i) (.inl i') + bE b (.inr (.inl i)) (.inr (.inl i'))) * N =
          N * (bE b (.inl i) (.inl i') + bE b (.inr (.inl i)) (.inr (.inl i'))) := by
      intro i i' hii'
      apply b.ext
      intro k
      rw [Module.End.mul_apply, Module.End.mul_apply]
      rcases k with j | j | j
      · rw [hb1, LinearMap.add_apply, LinearMap.add_apply, bE_basis, bE_basis, bE_basis,
          bE_basis]
        by_cases hj : j = i'
        · subst hj
          simp [hb1]
        · simp [hj]
      · rw [hb2, map_zero, LinearMap.add_apply, bE_basis, bE_basis]
        by_cases hj : j = i'
        · subst hj
          simp [hb2]
        · simp [hj]
      · rw [hb2, map_zero, LinearMap.add_apply, bE_basis, bE_basis]
        simp
    refine ⟨X, X', ?_, ?_, ?_, ?_, hcomm _ _ hi, hcomm _ _ hi.symm, ?_⟩
    · simp [X, add_mul, mul_add, bE_mul_bE, hi]
    · simp [X', add_mul, mul_add, bE_mul_bE, hi.symm]
    · simp [X, X', add_mul, mul_add, bE_mul_bE]
    · simp [X, X', add_mul, mul_add, bE_mul_bE]
    · intro h0
      have h1 := congrArg (fun T : Module.End K V => T (b (.inl i₁))) h0
      simp [X, bE_basis] at h1
      exact b.ne_zero _ h1

theorem invCentThree_SL {K : Type*} [Field K] [CharP K 2] {n : ℕ} (hn : 4 ≤ n) :
    InvCentThree (SpecialLinearGroup (Fin n) K) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro t ht
  set E := LinearMap.toMatrixAlgEquiv' (R := K) (n := Fin n) with hE
  set T : Matrix (Fin n) (Fin n) K := (t : Matrix (Fin n) (Fin n) K) with hTdef
  have hTT : T * T = 1 := by
    simpa using congrArg (fun g : SpecialLinearGroup (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) ht
  set N : Module.End K (Fin n → K) := E.symm T - 1 with hNdef
  have h2 : (2 : Module.End K (Fin n → K)) = 0 := end_two_eq_zero
  have hx : ∀ x : Module.End K (Fin n → K), x + x = 0 := fun x => by
    rw [← two_mul, h2, zero_mul]
  have hTT' : E.symm T * E.symm T = 1 := by rw [← map_mul, hTT, map_one]
  have hN : N * N = 0 := by
    rw [hNdef, sub_mul, mul_sub, mul_sub, hTT', mul_one, one_mul, one_mul]
    calc (1 : Module.End K (Fin n → K)) - E.symm T - (E.symm T - 1) =
        (1 + 1) - (E.symm T + E.symm T) := by abel
      _ = 0 := by rw [hx, hx, sub_zero]
  obtain ⟨X, X', hX, hX', h1, h1', hc, hc', hX0⟩ :=
    exists_matrixUnits_of_sq_eq_zero (by rw [Module.finrank_fin_fun]; exact hn) N hN
  obtain ⟨Y, hY⟩ : ∃ Y : Module.End K (Fin n → K), Y = (1 + X) * (1 + X') := ⟨_, rfl⟩
  have hdet : (E Y).det = 1 := by
    rw [show E Y = LinearMap.toMatrix' Y from rfl, LinearMap.det_toMatrix', hY]
    exact det_one_add_mul_one_add hX hX'
  obtain ⟨y, hyc⟩ : ∃ y : Matrix.SpecialLinearGroup (Fin n) K,
      (y : Matrix (Fin n) (Fin n) K) = E Y := ⟨⟨E Y, hdet⟩, rfl⟩
  have hT : E.symm T = 1 + N := by rw [hNdef]; abel
  have hYT : E Y * T = T * E Y := by
    apply E.symm.injective
    rw [map_mul, map_mul, AlgEquiv.symm_apply_apply, hT, mul_add, add_mul, mul_one, one_mul, hY,
      commute_prod hc hc']
  refine ⟨y, orderOf_eq_prime ?_ ?_, ?_⟩
  · have h3 : (E Y) ^ 3 = 1 := by rw [← map_pow, hY, cube_eq_one h2 hX hX' h1 h1', map_one]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hyc, h3, Matrix.SpecialLinearGroup.coe_one]
  · intro h
    have h3 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin n) K =>
      E.symm (g : Matrix (Fin n) (Fin n) K)) h
    simp only [Matrix.SpecialLinearGroup.coe_one, map_one, hyc, AlgEquiv.symm_apply_apply] at h3
    rw [hY] at h3
    exact ne_one h2 hX h1 hX0 h3
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hyc, ← hTdef, hYT]

section Symm

variable {K : Type*} [Field K] {n : ℕ}

theorem transpose_mul_mul_eq_of_forall {M R : Matrix (Fin n) (Fin n) K}
    (h : ∀ v w, (M *ᵥ v) ⬝ᵥ (R *ᵥ (M *ᵥ w)) = v ⬝ᵥ (R *ᵥ w)) : Mᵀ * R * M = R := by
  refine ext_iff_mulVec.mpr fun w => dotProduct_eq_iff.mp fun u => ?_
  rw [dotProduct_comm _ u, dotProduct_comm _ u, ← mulVec_mulVec, ← mulVec_mulVec,
    dotProduct_mulVec, vecMul_transpose]
  exact h u w

theorem dotProduct_mulVec_comm {R : Matrix (Fin n) (Fin n) K} (hRs : Rᵀ = R) (u v : Fin n → K) :
    u ⬝ᵥ (R *ᵥ v) = v ⬝ᵥ (R *ᵥ u) := by
  rw [dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose, hRs]

@[expose] def symmForm (R : Matrix (Fin n) (Fin n) K) (hRs : Rᵀ = R) (hR : IsUnit R.det) :
    ReflForm K (Fin n → K) where
  σ := RingEquiv.refl K
  β u v := u ⬝ᵥ (R *ᵥ v)
  add_left u u' v := add_dotProduct u u' _
  smul_left c u v := smul_dotProduct c u _
  add_right u v v' := by rw [mulVec_add, dotProduct_add]
  smul_right c u v := by rw [mulVec_smul, dotProduct_smul, smul_eq_mul]
  refl u v h := by rw [dotProduct_mulVec_comm hRs, h]
  nondeg u h := by
    have hR' : u ᵥ* R = 0 := by
      ext i
      have h1 := h (Pi.single i 1)
      rwa [dotProduct_mulVec, dotProduct_single, mul_one] at h1
    have h2 := congrArg (· ᵥ* R⁻¹) hR'
    simpa [vecMul_vecMul, mul_nonsing_inv R hR] using h2

theorem exists_sl_symm_order_three [Finite K] [CharP K 2] (hn : 3 ≤ n)
    (R : Matrix (Fin n) (Fin n) K) (hRs : Rᵀ = R) (hR : IsUnit R.det) :
    ∃ g : Matrix.SpecialLinearGroup (Fin n) K, g ^ 3 = 1 ∧ g ≠ 1 ∧
      (g : Matrix (Fin n) (Fin n) K)ᵀ * R * g = R := by
  set F := symmForm R hRs hR with hF
  have hσ : ∀ c, F.σ c = c := fun c => rfl
  have hsymm : ∀ u v, F.β u v = F.β v u := fun u v => dotProduct_mulVec_comm hRs u v
  obtain ⟨H, hHmem, hHdim⟩ := exists_ker_sqrt (fun v => F.β v v)
    (fun u v => by
      rw [F.add_left, F.add_right, F.add_right, hsymm v u]
      linear_combination F.β u v * CharTwo.two_eq_zero (R := K))
    (fun c v => by rw [F.smul_left, F.smul_right, hσ]; ring)
  rw [Module.finrank_fin_fun] at hHdim
  obtain ⟨u, hu, u', hu', huu'⟩ := exists_eq_one F LinearMap.id H (by
    rw [Module.finrank_fin_fun]; exact hHdim) (by rw [Submodule.map_id]; omega)
  rw [LinearMap.id_apply] at huu'
  have huu : F.β u u = 0 := (hHmem u).mp hu
  have hu'u' : F.β u' u' = 0 := (hHmem u').mp hu'
  have hu'u : F.β u' u = 1 := by rw [hsymm, huu']
  have h2 : (2 : Module.End K (Fin n → K)) = 0 := end_two_eq_zero
  have hX := tv_mul_self F huu
  have hX' := tv_mul_self F hu'u'
  have h1 := tv_mul_tv_mul_tv F (e := u) (e' := u') (by rw [huu', hu'u, one_mul])
  have h1' := tv_mul_tv_mul_tv F (e := u') (e' := u) (by rw [huu', hu'u, one_mul])
  obtain ⟨Y, hY⟩ : ∃ Y : Module.End K (Fin n → K), Y = (1 + tv F u) * (1 + tv F u') := ⟨_, rfl⟩
  set E := LinearMap.toMatrixAlgEquiv' (R := K) (n := Fin n) with hE
  have hdet : (E Y).det = 1 := by
    rw [show E Y = LinearMap.toMatrix' Y from rfl, LinearMap.det_toMatrix', hY]
    exact det_one_add_mul_one_add hX hX'
  obtain ⟨g, hgc⟩ : ∃ g : Matrix.SpecialLinearGroup (Fin n) K,
      (g : Matrix (Fin n) (Fin n) K) = E Y := ⟨⟨E Y, hdet⟩, rfl⟩
  have hYv : ∀ v, E Y *ᵥ v = Y v := fun v => LinearMap.toMatrix'_mulVec Y v
  refine ⟨g, ?_, ?_, ?_⟩
  · have h3 : (E Y) ^ 3 = 1 := by rw [← map_pow, hY, cube_eq_one h2 hX hX' h1 h1', map_one]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hgc, h3, Matrix.SpecialLinearGroup.coe_one]
  · intro h
    have h3 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin n) K =>
      E.symm (g : Matrix (Fin n) (Fin n) K)) h
    simp only [Matrix.SpecialLinearGroup.coe_one, map_one, hgc, AlgEquiv.symm_apply_apply] at h3
    rw [hY] at h3
    exact ne_one h2 hX h1 (tv_ne_zero F huu') h3
  · rw [hgc]
    refine transpose_mul_mul_eq_of_forall fun v w => ?_
    rw [hYv, hYv, hY]
    change F.β (((1 + tv F u) * (1 + tv F u')) v) (((1 + tv F u) * (1 + tv F u')) w) = F.β v w
    rw [Module.End.mul_apply, Module.End.mul_apply, tv_isometry F hσ hsymm huu,
      tv_isometry F hσ hsymm hu'u']

end Symm

@[expose] def c4 : Equiv.Perm (Fin 4) := ⟨![1, 2, 0, 3], ![2, 0, 1, 3], by decide, by decide⟩

theorem c4_cube : c4 * c4 * c4 = 1 := by decide

theorem c4_mul_inv : c4 * c4⁻¹ = 1 := mul_inv_cancel c4

theorem sign_c4 : Equiv.Perm.sign c4 = 1 := by decide

section Perm

variable (K : Type*) [Field K]

@[expose] def p4 : Matrix.SpecialLinearGroup (Fin 4) K :=
  ⟨c4.permMatrix K, by rw [det_permutation, sign_c4]; simp⟩

theorem coe_p4 : (p4 K : Matrix (Fin 4) (Fin 4) K) = c4.permMatrix K := rfl

variable {K}

theorem p4_pow_three : p4 K ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, coe_p4, pow_three,
    ← permMatrix_mul, ← permMatrix_mul, c4_cube, permMatrix_one]

theorem p4_ne_one : p4 K ≠ 1 := by
  intro h
  have h1 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 4) K =>
    (g : Matrix (Fin 4) (Fin 4) K) 0 1) h
  simp [coe_p4, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, c4] at h1

theorem map_p4 (σ : K ≃+* K) : Matrix.SpecialLinearGroup.map σ.toRingHom (p4 K) = p4 K := by
  apply Subtype.ext
  change (c4.permMatrix K).map σ = c4.permMatrix K
  ext i j
  simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  split_ifs <;> simp

theorem inv_transpose_p4 : (p4 K)⁻¹.transpose = p4 K := by
  have h : (p4 K).transpose * p4 K = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_transpose,
      Matrix.SpecialLinearGroup.coe_one, coe_p4, transpose_permMatrix, ← permMatrix_mul,
      c4_mul_inv, permMatrix_one]
  rw [← eq_inv_of_mul_eq_one_left h]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_transpose, Matrix.SpecialLinearGroup.coe_transpose,
    transpose_transpose]

theorem fieldAut_proj_p4 (σ : K ≃+* K) : fieldAut 4 K σ (proj 4 K (p4 K)) = proj 4 K (p4 K) := by
  rw [fieldAut_proj, map_p4]

theorem dualAut_proj_p4 : dualAut 4 K (proj 4 K (p4 K)) = proj 4 K (p4 K) := by
  rw [dualAut_proj, inv_transpose_p4]

end Perm

open CFSG.RankThree.PartTwo.KFacts.KS21.L44 (F4 PL)

theorem scalars_F4 : scalars 4 F4 = ⊥ := by
  rw [scalars_eq_center]
  exact CFSG.RankThree.PartTwo.KFacts.KS21.L44.center_M

theorem proj_injective_F4 : Function.Injective (proj 4 F4) :=
  (MonoidHom.ker_eq_bot_iff _).mp (by rw [ker_proj, scalars_F4])

@[expose] def equivSL_PL : PL ≃* Matrix.SpecialLinearGroup (Fin 4) F4 :=
  (QuotientGroup.quotientMulEquivOfEq scalars_F4).trans QuotientGroup.quotientBot

theorem invCentThree_PL : InvCentThree PL :=
  (invCentThree_SL (K := F4) (le_refl 4)).of_mulEquiv equivSL_PL.symm

theorem orderOf_proj_p4 : orderOf (proj 4 F4 (p4 F4)) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [orderOf_injective _ proj_injective_F4]
  exact orderOf_eq_prime p4_pow_three p4_ne_one

theorem invFixThree_PL : InvFixThree PL := by
  intro α hα
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hα2 : α ^ 2 = 1 := by
    have h := pow_orderOf_eq_one α
    rwa [hα] at h
  have hK : Nat.card F4 = 2 ^ 2 := by
    rw [CFSG.RankThree.PartTwo.KFacts.KS21.L44.card_F4]; norm_num
  obtain ⟨-, hgen⟩ := automorphism_generation (K := F4) (n := 4) (by norm_num)
  obtain ⟨A, σ, ε, hε, rfl⟩ := hgen α
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  · rw [pow_zero, mul_one] at hα hα2 ⊢
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one, mul_one] at hα ⊢
      obtain ⟨x, hx⟩ := CFSG.RankThree.PartTwo.KFacts.KS21.L44.conjAut_mem_range A
      rw [← hx] at hα ⊢
      exact conj_fix CFSG.RankThree.PartTwo.KFacts.KS21.L44.center_PL invCentThree_PL x hα
    · obtain ⟨-, -, H, hH⟩ :=
        even_linear_field_involution_descent (f := 2) (by norm_num) hK (by norm_num) A σ hσ hα2
      exact ⟨conjAut 4 F4 H (proj 4 F4 (p4 F4)), by rw [MulEquiv.orderOf_eq]; exact orderOf_proj_p4,
        fix_of_conj hH (fieldAut_proj_p4 σ)⟩
  · rw [pow_one] at hα hα2 ⊢
    by_cases hσ : σ = 1
    · subst hσ
      rw [map_one, mul_one] at hα hα2 ⊢
      have hneg : -(A : Matrix (Fin 4) (Fin 4) F4) = A := by
        ext i j
        rw [Matrix.neg_apply, CharTwo.neg_eq]
      have hAs : (A : Matrix (Fin 4) (Fin 4) F4)ᵀ = A := by
        rcases transpose_eq_or_eq_neg_of_sq_conjAut_dualAut (by norm_num) A hα2 with h | h
        · exact h
        · rw [h, hneg]
      have hRs : ((A⁻¹ : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4)ᵀ = (A⁻¹ : GL (Fin 4) F4) := by
        rw [Matrix.coe_units_inv, transpose_nonsing_inv, hAs]
      have hRu : IsUnit ((A⁻¹ : GL (Fin 4) F4) : Matrix (Fin 4) (Fin 4) F4).det :=
        (Matrix.isUnit_iff_isUnit_det _).mp (A⁻¹).isUnit
      obtain ⟨g, hg3, hg1, hgR⟩ := exists_sl_symm_order_three (by norm_num) _ hRs hRu
      refine ⟨proj 4 F4 g, ?_, conjAut_dualAut_proj_of_transpose_mul_mul A g hgR⟩
      rw [orderOf_injective _ proj_injective_F4]
      exact orderOf_eq_prime hg3 hg1
    · obtain ⟨-, -, H, hH⟩ := odd_linear_graph_field_involution_conjugacy Nat.prime_two (f := 2)
        (by norm_num) hK (by norm_num) A σ hσ hα2
      exact ⟨conjAut 4 F4 H (proj 4 F4 (p4 F4)), by rw [MulEquiv.orderOf_eq]; exact orderOf_proj_p4,
        fix_of_conj hH (by rw [MulAut.mul_apply, dualAut_proj_p4, fieldAut_proj_p4])⟩

theorem invFixThree_projSL : InvFixThree (CFSG.Assembly.RankThreeEven.projSL 4 F4) :=
  invFixThree_PL.of_mulEquiv (CFSG.RankThree.PartTwo.Sec4.projSLEquivProjectiveSL 4 F4)

end CFSG.RankThree.PartTwo.Sec21.AS76.L44
