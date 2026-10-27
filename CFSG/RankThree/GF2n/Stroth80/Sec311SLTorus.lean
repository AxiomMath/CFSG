module

public import CFSG.Open.StatedDefs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open
open scoped Matrix

theorem exists_gl_mem_statedSL_of_det {m : ℕ} {K : Type} [Field K]
    {M : Matrix (Fin m) (Fin m) K} (hM : M.det = 1) :
    ∃ g ∈ StatedSL m K, (g : Matrix (Fin m) (Fin m) K) = M := by
  have hne : M.det ≠ 0 := by
    rw [hM]
    exact one_ne_zero
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hne, ?_, rfl⟩
  unfold StatedSL
  exact Subgroup.subset_closure (by simpa using hM)

theorem mulVec_transvec_eq {m : ℕ} {K : Type} [Field K] (u v x : Fin m → K) :
    (1 + Matrix.replicateCol Unit u * Matrix.replicateRow Unit v :
      Matrix (Fin m) (Fin m) K) *ᵥ x = x + (v ⬝ᵥ x) • u := by
  rw [Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
  have hB : Matrix.replicateRow Unit v *ᵥ x = fun _ : Unit => v ⬝ᵥ x := by
    funext _
    simp [Matrix.mulVec, dotProduct, Matrix.replicateRow]
  rw [hB]
  funext i
  simp [Matrix.mulVec, dotProduct, Matrix.replicateCol, mul_comm]

theorem det_transvec_eq_one {m : ℕ} {K : Type} [Field K] (u v : Fin m → K)
    (huv : v ⬝ᵥ u = 0) :
    (1 + Matrix.replicateCol Unit u * Matrix.replicateRow Unit v :
      Matrix (Fin m) (Fin m) K).det = 1 := by
  rw [Matrix.det_one_add_replicateCol_mul_replicateRow, huv, add_zero]

theorem exists_det_one_pivot {m : ℕ} {K : Type} [Field K] (p : Fin m) {x : Fin m → K}
    (hx : x p ≠ 0) :
    ∃ M : Matrix (Fin m) (Fin m) K, M.det = 1 ∧ M *ᵥ x = Pi.single p (x p) := by
  refine ⟨1 + Matrix.replicateCol Unit
      (fun i => -((x p)⁻¹ * (x i - (Pi.single p (x p) : Fin m → K) i)))
      * Matrix.replicateRow Unit (Pi.single p (1 : K)), ?_, ?_⟩
  · apply det_transvec_eq_one
    simp [single_dotProduct]
  · rw [mulVec_transvec_eq, single_dotProduct, one_mul]
    funext i
    have hinv : x p * (x p)⁻¹ = 1 := mul_inv_cancel₀ hx
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (-(x i - (Pi.single p (x p) : Fin m → K) i)) * hinv

theorem exists_det_one_scale {m : ℕ} {K : Type} [Field K] {p q : Fin m} (hpq : p ≠ q)
    {a : K} (ha : a ≠ 0) :
    ∃ D : Matrix (Fin m) (Fin m) K, D.det = 1 ∧ D *ᵥ Pi.single p a = Pi.single p 1 := by
  refine ⟨Matrix.diagonal (fun i => (if i = p then a⁻¹ else 1) * (if i = q then a else 1)),
    ?_, ?_⟩
  · rw [Matrix.det_diagonal]
    simp only [Finset.prod_mul_distrib]
    simp [Finset.prod_ite_eq', ha]
  · funext i
    by_cases hi : i = p
    · simp [hi, hpq, ha, Matrix.mulVec_diagonal, Pi.single_apply]
    · simp [hi, Matrix.mulVec_diagonal, Pi.single_apply]

theorem exists_det_one_pivot_single {m : ℕ} {K : Type} [Field K] {p q : Fin m}
    (hpq : p ≠ q) {x : Fin m → K} (hx : x p ≠ 0) :
    ∃ M : Matrix (Fin m) (Fin m) K, M.det = 1 ∧ M *ᵥ x = Pi.single p 1 := by
  obtain ⟨M₁, hM₁, hM₁x⟩ := exists_det_one_pivot p hx
  obtain ⟨D, hD, hDe⟩ := exists_det_one_scale hpq hx
  refine ⟨D * M₁, by rw [Matrix.det_mul, hD, hM₁, one_mul], ?_⟩
  rw [← Matrix.mulVec_mulVec, hM₁x, hDe]

theorem exists_det_one_move_pivot {m : ℕ} {K : Type} [Field K] {p j : Fin m} (hjp : j ≠ p)
    {x : Fin m → K} (hp : x p = 0) (hj : x j ≠ 0) :
    ∃ T : Matrix (Fin m) (Fin m) K, T.det = 1 ∧ (T *ᵥ x) p ≠ 0 := by
  refine ⟨1 + Matrix.replicateCol Unit (Pi.single p (1 : K))
      * Matrix.replicateRow Unit (Pi.single j (1 : K)), ?_, ?_⟩
  · apply det_transvec_eq_one
    simp [single_dotProduct, Pi.single_apply, hjp]
  · rw [mulVec_transvec_eq]
    simp [single_dotProduct, hp, hj]

theorem exists_det_one_mulVec_eq_single {m : ℕ} {K : Type} [Field K] {p q : Fin m}
    (hpq : p ≠ q) {x : Fin m → K} (hx : x ≠ 0) :
    ∃ M : Matrix (Fin m) (Fin m) K, M.det = 1 ∧ M *ᵥ x = Pi.single p 1 := by
  by_cases hp : x p = 0
  · obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
      by_contra h
      exact hx (funext fun j => Classical.byContradiction fun hj => h ⟨j, hj⟩)
    have hjp : j ≠ p := fun h => hj (by rw [h]; exact hp)
    obtain ⟨T, hT, hTp⟩ := exists_det_one_move_pivot hjp hp hj
    obtain ⟨N, hN, hNx⟩ := exists_det_one_pivot_single hpq (x := T *ᵥ x) hTp
    refine ⟨N * T, by rw [Matrix.det_mul, hN, hT, one_mul], ?_⟩
    rw [← Matrix.mulVec_mulVec, hNx]
  · exact exists_det_one_pivot_single hpq hp

theorem exists_statedSL_mulVec_single {K : Type} [Field K] {m : ℕ} {p q : Fin m}
    (hpq : p ≠ q) {x : Fin m → K} (hx : x ≠ 0) :
    ∃ g ∈ StatedSL m K, (g : Matrix (Fin m) (Fin m) K) *ᵥ x = Pi.single p 1 := by
  obtain ⟨M, hM, hMx⟩ := exists_det_one_mulVec_eq_single hpq hx
  obtain ⟨g, hgS, hg⟩ := exists_gl_mem_statedSL_of_det hM
  exact ⟨g, hgS, by rw [hg, hMx]⟩

theorem exists_statedSL_mulVec_eq_of_ne_zero {K : Type} [Field K] {m : ℕ} (hm : 2 ≤ m)
    {x y : Fin m → K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ g ∈ StatedSL m K, (g : Matrix (Fin m) (Fin m) K) *ᵥ x = y := by
  obtain ⟨p, q, hpq⟩ : ∃ p q : Fin m, p ≠ q :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩
  obtain ⟨gx, hgxS, hgx⟩ := exists_statedSL_mulVec_single hpq hx
  obtain ⟨gy, hgyS, hgy⟩ := exists_statedSL_mulVec_single hpq hy
  refine ⟨gy⁻¹ * gx, Subgroup.mul_mem _ (Subgroup.inv_mem _ hgyS) hgxS, ?_⟩
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, hgx, ← hgy, Matrix.mulVec_mulVec, Units.inv_mul,
    Matrix.one_mulVec]

theorem exists_torus_entries {K : Type} [Field K] {m : ℕ} {p q : Fin m} (hpq : p ≠ q)
    {a : K} (ha0 : a ≠ 0) :
    ∃ t : Fin m → K, t p = a ∧ t q = a⁻¹ ∧ (∀ i, i ≠ p → i ≠ q → t i = 1) ∧
      ∏ i, t i = 1 := by
  refine ⟨fun i => (if i = p then a else 1) * (if i = q then a⁻¹ else 1), ?_, ?_, ?_, ?_⟩
  · simp [hpq]
  · simp [hpq.symm]
  · intro i hi hj
    simp [hi, hj]
  · simp only [Finset.prod_mul_distrib]
    simp [Finset.prod_ite_eq, Finset.prod_ite_eq', ha0]

theorem eq_one_of_elation_comm_torus {K : Type} [Field K] [CharP K 2] {m : ℕ} {p q : Fin m}
    (hpq : p ≠ q) {a : K} (ha0 : a ≠ 0) (ha1 : a ≠ 1) {t : Fin m → K} (htp : t p = a)
    (htq : t q = a⁻¹) (hto : ∀ i, i ≠ p → i ≠ q → t i = 1) {M : Matrix (Fin m) (Fin m) K}
    (hfix : M *ᵥ Pi.single p 1 = Pi.single p 1)
    (helat : ∀ x : Fin m → K, ∃ c : K, M *ᵥ x - x = c • Pi.single p 1)
    (hcomm : Matrix.diagonal t * M = M * Matrix.diagonal t) : M = 1 := by
  have hne : a - a⁻¹ ≠ 0 := by
    intro h
    have h1 : a⁻¹ = a := (sub_eq_zero.mp h).symm
    have h2 : a * a = 1 := by
      calc a * a = a * a⁻¹ := by rw [h1]
        _ = 1 := mul_inv_cancel₀ ha0
    have h3 : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
    have h4 : (a - 1) * (a - 1) = 0 := by linear_combination h2 + (1 - a) * h3
    exact ha1 (sub_eq_zero.mp (mul_self_eq_zero.mp h4))
  have hmulsingle : ∀ j i, (M *ᵥ Pi.single j (1 : K)) i = M i j := by
    intro j i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, Finset.sum_ite_eq']
  have hrow : ∀ i j, i ≠ p → M i j = (Pi.single j (1 : K) : Fin m → K) i := by
    intro i j hi
    obtain ⟨c, hc⟩ := helat (Pi.single j 1)
    have h1 := congrFun hc i
    have h3 : (c • (Pi.single p (1 : K) : Fin m → K)) i = 0 := by
      simp [Pi.single_apply, hi]
    rw [Pi.sub_apply, hmulsingle, h3] at h1
    exact sub_eq_zero.mp h1
  have hpp : M p p = 1 := by
    have h := congrFun hfix p
    rw [hmulsingle, Pi.single_eq_same] at h
    exact h
  have hrowp : ∀ j, j ≠ p → M p j = 0 := by
    intro j hj
    have h := congrFun (congrFun hcomm p) j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, htp] at h
    by_cases hjq : j = q
    · have htj : t j = a⁻¹ := by rw [hjq]; exact htq
      rw [htj] at h
      have h' : (a - a⁻¹) * M p j = 0 := by linear_combination h
      exact (mul_eq_zero.mp h').resolve_left hne
    · have htj : t j = 1 := hto j hj hjq
      rw [htj, mul_one] at h
      have h' : (a - 1) * M p j = 0 := by linear_combination h
      exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr ha1)
  ext i j
  rw [Matrix.one_apply]
  by_cases hi : i = p
  · rw [hi]
    by_cases hj : j = p
    · rw [hj]
      simp [hpp]
    · rw [hrowp j hj]
      simp [hj, Ne.symm hj]
  · rw [hrow i j hi, Pi.single_apply]

theorem exists_torus_statedSL {K : Type} [Field K] [CharP K 2] {m : ℕ} (hm : 2 ≤ m)
    {u : Fin m → K} (hu : u ≠ 0) {a : K} (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    ∃ T ∈ StatedSL m K, (T : Matrix (Fin m) (Fin m) K) *ᵥ u = a • u ∧
      ∀ g : GL (Fin m) K, (g : Matrix (Fin m) (Fin m) K) *ᵥ u = u →
        (∀ x : Fin m → K, ∃ c : K, (g : Matrix (Fin m) (Fin m) K) *ᵥ x - x = c • u) →
        T * g = g * T → g = 1 := by
  obtain ⟨p, q, hpq⟩ : ∃ p q : Fin m, p ≠ q :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩
  obtain ⟨t, htp, htq, hto, htdet⟩ := exists_torus_entries hpq ha0
  obtain ⟨T0, hT0S, hT0⟩ := exists_gl_mem_statedSL_of_det (M := Matrix.diagonal t)
    (by rw [Matrix.det_diagonal]; exact htdet)
  obtain ⟨g0, hg0S, hg0⟩ := exists_statedSL_mulVec_single hpq hu
  have hTe : Matrix.diagonal t *ᵥ Pi.single p 1 = a • Pi.single p 1 := by
    funext i
    by_cases hi : i = p
    · simp [hi, htp, Matrix.mulVec_diagonal]
    · simp [hi, Matrix.mulVec_diagonal, Pi.single_apply]
  refine ⟨g0⁻¹ * T0 * g0,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg0S) hT0S) hg0S, ?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg0, hT0,
      hTe, Matrix.mulVec_smul, ← hg0, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  · intro g hgu hgel hcomm
    have hgg : ∀ v : Fin m → K,
        (g0 : Matrix (Fin m) (Fin m) K) *ᵥ
          (((g0⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ v) = v := by
      intro v
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have hginv : ∀ v : Fin m → K,
        ((g0⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ
          ((g0 : Matrix (Fin m) (Fin m) K) *ᵥ v) = v := by
      intro v
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    have hconj : ∀ v : Fin m → K,
        ((g0 * g * g0⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ v =
          (g0 : Matrix (Fin m) (Fin m) K) *ᵥ ((g : Matrix (Fin m) (Fin m) K) *ᵥ
            (((g0⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ v)) := by
      intro v
      rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have hfixG : ((g0 * g * g0⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ
        Pi.single p 1 = Pi.single p 1 := by
      rw [hconj, ← hg0, hginv, hgu]
    have helatG : ∀ x : Fin m → K, ∃ c : K,
        ((g0 * g * g0⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ x - x =
          c • Pi.single p 1 := by
      intro x
      obtain ⟨c, hc⟩ := hgel (((g0⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ x)
      refine ⟨c, ?_⟩
      have h2 : (g0 : Matrix (Fin m) (Fin m) K) *ᵥ
          ((g : Matrix (Fin m) (Fin m) K) *ᵥ
            (((g0⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ x)) - x =
          (g0 : Matrix (Fin m) (Fin m) K) *ᵥ
            ((g : Matrix (Fin m) (Fin m) K) *ᵥ
              (((g0⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ x) -
              ((g0⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) *ᵥ x) := by
        rw [Matrix.mulVec_sub, hgg x]
      rw [hconj, ← hg0, h2, hc, Matrix.mulVec_smul]
    have hGG : T0 * (g0 * g * g0⁻¹) = g0 * g * g0⁻¹ * T0 := by
      calc T0 * (g0 * g * g0⁻¹) = g0 * (g0⁻¹ * T0 * g0 * g) * g0⁻¹ := by group
        _ = g0 * (g * (g0⁻¹ * T0 * g0)) * g0⁻¹ := by rw [hcomm]
        _ = g0 * g * g0⁻¹ * T0 := by group
    have hcommM : Matrix.diagonal t *
        ((g0 * g * g0⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) =
        ((g0 * g * g0⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) * Matrix.diagonal t := by
      have h := congrArg Units.val hGG
      simpa only [Units.val_mul, hT0] using h
    have hG1 : ((g0 * g * g0⁻¹ : GL (Fin m) K) : Matrix (Fin m) (Fin m) K) = 1 :=
      eq_one_of_elation_comm_torus hpq ha0 ha1 htp htq hto hfixG helatG hcommM
    have hG1' : g0 * g * g0⁻¹ = 1 := Units.ext (by rw [hG1, Units.val_one])
    calc g = g0⁻¹ * (g0 * g * g0⁻¹) * g0 := by group
      _ = g0⁻¹ * 1 * g0 := by rw [hG1']
      _ = 1 := by group

end CFSG.RankThree.GF2n.Stroth80
