module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightF8TwoOmega

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.Open CFSG.Quasithin CFSG.ComponentClassification.RankTwoClassical
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K]

theorem s16k_commute_oRhoTwoGL_oRhoOneGL [CharP K 2] {ι₂ ι : Type} [Fintype ι₂]
    [DecidableEq ι₂] [Fintype ι] [DecidableEq ι] (oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι)
    (A B : SL(2, K)) : Commute (oRhoTwoGL oe A) (oRhoOneGL oe B) := by
  apply Units.ext
  change oblk oe 1 (rhoTwoMat A) * oblk oe 1 (rhoOneMat B) =
    oblk oe 1 (rhoOneMat B) * oblk oe 1 (rhoTwoMat A)
  rw [oblk_mul, oblk_mul, Matrix.one_mul, rhoOne_mul_rhoTwo]

theorem s16k_oRhoTwoGL_injective {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
    [Fintype ι] [DecidableEq ι] (oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι) :
    Function.Injective (oRhoTwoGL (K := K) oe) := by
  intro A A' h
  have h1 := congrArg (fun x : GL ι K => (x : Matrix ι ι K)) h
  simp only [coe_oRhoTwoGL] at h1
  have h2 := (oblk_injective h1).2
  rw [rhoTwoMat_apply, rhoTwoMat_apply, fromBlocks_inj] at h2
  exact Subtype.ext h2.1

theorem s16k_oRhoOneGL_injective {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
    [Fintype ι] [DecidableEq ι] (oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι) :
    Function.Injective (oRhoOneGL (K := K) oe) := by
  intro B B' h
  have h1 := congrArg (fun x : GL ι K => (x : Matrix ι ι K)) h
  simp only [coe_oRhoOneGL] at h1
  have h2 := (oblk_injective h1).2
  rw [rhoOneMat_apply, rhoOneMat_apply, fromBlocks_inj] at h2
  obtain ⟨e1, e2, e3, e4⟩ := h2
  have f1 := congrFun (congrFun e1 0) 0
  have f2 := congrFun (congrFun e2 0) 1
  have f3 := congrFun (congrFun e3 1) 0
  have f4 := congrFun (congrFun e4 0) 0
  simp [swapM] at f1 f2 f3 f4
  ext i j
  fin_cases i <;> fin_cases j
  · exact f1
  · exact f2
  · exact f3
  · exact f4

theorem s16k_transpose_inv_pow {A : SL(2, K)} {n : ℕ} (h : A ^ n = 1) :
    (Matrix.SpecialLinearGroup.transpose A⁻¹) ^ n = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_transpose,
    ← Matrix.transpose_pow, ← Matrix.SpecialLinearGroup.coe_pow, inv_pow, h, inv_one]
  simp

theorem s16k_single_ne_zero_om {ι : Type} [DecidableEq ι] (i : ι) :
    (Pi.single i 1 : ι → K) ≠ 0 := fun h => by
  have h1 := congrFun h i
  simp at h1

theorem s16k_zpowers_pow_eq_one {G : Type*} [Group G] {x : G} {p : ℕ}
    (hx : orderOf x = p) {z : G} (hz : z ∈ Subgroup.zpowers x) : z ^ p = 1 := by
  have hdvd : orderOf z ∣ orderOf x := orderOf_dvd_of_mem_zpowers hz
  rw [hx] at hdvd
  exact orderOf_dvd_iff_pow_eq_one.1 hdvd

theorem s16k_isometry_of_mem_zpowers {κ : Type} [Fintype κ] [DecidableEq κ]
    {R : (κ → K) → K} {x : Matrix.GeneralLinearGroup κ K}
    (hx : ∀ v, R ((x : Matrix κ κ K) *ᵥ v) = R v) {z : Matrix.GeneralLinearGroup κ K}
    (hz : z ∈ Subgroup.zpowers x) (v : κ → K) : R ((z : Matrix κ κ K) *ᵥ v) = R v := by
  have hxcl : x ∈ Subgroup.closure {A : Matrix.GeneralLinearGroup κ K |
      ∀ v, R ((A : Matrix κ κ K) *ᵥ v) = R v} := Subgroup.subset_closure hx
  exact quad_mulVec_of_mem_closure (R := R) (M := z) (Subgroup.zpowers_le.2 hxcl hz) v

theorem s16k_omega_blocks [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
    [Fintype ι] [DecidableEq ι] (oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι) {Q : (ι → K) → K}
    {Q₂ : (ι₂ → K) → K}
    (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) +
      StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
    {p : ℕ} (hp : p.Prime) (hpK : p ∣ Nat.card K ^ 2 - 1) :
    ∃ x y : Matrix.GeneralLinearGroup ι K,
      (∀ v, Q ((x : Matrix ι ι K) *ᵥ v) = Q v) ∧
      (∀ v, Q ((y : Matrix ι ι K) *ᵥ v) = Q v) ∧
      Commute x y ∧ orderOf x = p ∧ orderOf y = p ∧ y ∉ Subgroup.zpowers x ∧
      ∀ v : ι → K, (∀ b, v (oe (.inr b)) = 0) →
        (x : Matrix ι ι K) *ᵥ v = v ∧ (y : Matrix ι ι K) *ᵥ v = v := by
  obtain ⟨g, hg⟩ := CFSG.HardMathSupport.Seitz.Proving.exists_orderOf_eq_prime_SL2 hp hpK
  refine ⟨oRhoTwoGL oe g, oRhoOneGL oe g, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    rw [coe_oRhoTwoGL]
    exact quad_oblk_mulVec_eq hQ (fun w => by simp) (quadPlus_two_rhoTwo g) v
  · intro v
    rw [coe_oRhoOneGL]
    exact quad_oblk_mulVec_eq hQ (fun w => by simp) (quadPlus_two_rhoOne g) v
  · exact s16k_commute_oRhoTwoGL_oRhoOneGL oe g g
  · rw [orderOf_injective (oRhoTwoGL oe) (s16k_oRhoTwoGL_injective oe) g, hg]
  · rw [orderOf_injective (oRhoOneGL oe) (s16k_oRhoOneGL_injective oe) g, hg]
  · intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have h1 : oRhoTwoGL oe (g ^ k) = oRhoOneGL oe g := by
      rw [map_zpow]
      exact hk
    have h2 := congrArg (fun z : GL ι K => (z : Matrix ι ι K)) h1
    simp only [coe_oRhoTwoGL, coe_oRhoOneGL] at h2
    have h3 := (oblk_injective h2).2
    have h4 : rhoTwoMat ((g ^ k)⁻¹) * rhoOneMat g = 1 := by
      rw [← h3, ← map_mul, inv_mul_cancel, map_one]
    rw [(s16g_rhoTwo_mul_rhoOne_eq_one h4).2, orderOf_one] at hg
    exact hp.one_lt.ne hg
  · intro v hv
    have key : ∀ X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K, oblk oe 1 X *ᵥ v = v := by
      intro X
      funext i
      obtain ⟨j, rfl⟩ := oe.surjective i
      rcases j with a | b
      · rw [oblk_mulVec_inl, Matrix.one_mulVec]
      · rw [oblk_mulVec_inr, show (fun b' => v (oe (.inr b'))) = 0 from funext hv,
          Matrix.mulVec_zero, hv b]
        rfl
    exact ⟨key _, key _⟩

theorem s16k_omega_fixed_singular [CharP K 2] {ι₂ ι : Type} [Fintype ι₂]
    [DecidableEq ι₂] [Fintype ι] [DecidableEq ι] (oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι)
    {Q : (ι → K) → K} {Q₂ : (ι₂ → K) → K}
    (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) +
      StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
    {p : ℕ} (hp : p.Prime) (hpK : p ∣ Nat.card K ^ 2 - 1) {u₂ : ι₂ → K}
    (hu₂ : Q₂ u₂ = 1) :
    ∃ g : Matrix.GeneralLinearGroup ι K,
      (∀ v, Q ((g : Matrix ι ι K) *ᵥ v) = Q v) ∧ orderOf g = p ∧
      ∃ u : ι → K, u ≠ 0 ∧ Q u = 0 ∧ (g : Matrix ι ι K) *ᵥ u = u := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨A, hA⟩ := CFSG.HardMathSupport.Seitz.Proving.exists_orderOf_eq_prime_SL2 hp hpK
  have hA1 : A ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hA
    exact hp.one_lt.ne hA
  have hApow : A ^ p = 1 := by rw [← hA]; exact pow_orderOf_eq_one A
  set B : SL(2, K) := Matrix.SpecialLinearGroup.transpose A⁻¹ with hB
  have hcomm : Commute (oRhoTwoGL oe A) (oRhoOneGL oe B) :=
    s16k_commute_oRhoTwoGL_oRhoOneGL oe A B
  set g : GL ι K := oRhoTwoGL oe A * oRhoOneGL oe B with hg
  have hcoe : (g : Matrix ι ι K) = oblk oe 1 (rhoTwoMat A * rhoOneMat B) := by
    change oblk oe 1 (rhoTwoMat A) * oblk oe 1 (rhoOneMat B) = _
    rw [oblk_mul, Matrix.one_mul]
  have hgQ : ∀ v, Q ((g : Matrix ι ι K) *ᵥ v) = Q v := by
    intro v
    rw [hcoe]
    exact quad_oblk_mulVec_eq hQ (fun w => by simp)
      (fun u => by rw [← Matrix.mulVec_mulVec, quadPlus_two_rhoTwo, quadPlus_two_rhoOne]) v
  have hpow : g ^ p = 1 := by
    rw [hg, hcomm.mul_pow, ← map_pow, ← map_pow, hApow, s16k_transpose_inv_pow hApow,
      map_one, map_one, one_mul]
  have hg1 : g ≠ 1 := by
    intro h
    have h1 := congrArg (fun z : GL ι K => (z : Matrix ι ι K)) h
    rw [hcoe] at h1
    have h2 := (oblk_injective (h1.trans (oblk_one (oe := oe)).symm)).2
    exact hA1 (s16g_rhoTwo_mul_rhoOne_eq_one h2).1
  refine ⟨g, hgQ, orderOf_eq_prime hpow hg1, ?_⟩
  let w₀ : Fin 2 ⊕ Fin 2 → K := Pi.single (Sum.inl 0) 1 + Pi.single (Sum.inr 0) 1
  let u : ι → K := fun i => Sum.elim u₂ w₀ (oe.symm i)
  have hu1 : ∀ a, u (oe (.inl a)) = u₂ a := fun a => by simp [u]
  have hu2 : ∀ b, u (oe (.inr b)) = w₀ b := fun b => by simp [u]
  have e1 : (fun a => u (oe (.inl a))) = u₂ := funext hu1
  have e2 : (fun b => u (oe (.inr b))) = w₀ := funext hu2
  refine ⟨u, ?_, ?_, ?_⟩
  · intro h
    have h1 := congrFun h (oe (.inr (.inl 0)))
    rw [hu2] at h1
    simp [w₀] at h1
  · have hq : StatedQuadPlus 2 K w₀ = 1 := by
      show ∑ i : Fin 2, w₀ (.inl i) * w₀ (.inr i) = 1
      simp [w₀, Fin.sum_univ_two]
    rw [hQ, e1, e2, hu₂, hq]
    exact CharTwo.add_self_eq_zero 1
  · funext i
    obtain ⟨j, rfl⟩ := oe.surjective i
    rw [hcoe]
    rcases j with a | b
    · rw [oblk_mulVec_inl, Matrix.one_mulVec]
    · rw [oblk_mulVec_inr, e2, s16g_rhoTwo_mul_rhoOne_fix A, hu2]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
