module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinLeviNormalizer

public section

namespace CFSG.StandardType.SpJoin

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl Matrix
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)
open scoped commutatorElement

variable {F : Type} [Field F]

private theorem det_sub_one_eq_trace [CharP F 2] (M : Matrix (Fin 2) (Fin 2) F) (hM : M.det = 1) :
    (M - 1).det = M.trace := by
  rw [Matrix.det_fin_two, Matrix.trace_fin_two]
  simp only [Matrix.sub_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero, CharTwo.sub_eq_add, CharTwo.neg_eq]
  have hM' : M 0 0 * M 1 1 + M 0 1 * M 1 0 = 1 := by
    rw [Matrix.det_fin_two] at hM
    rw [CharTwo.sub_eq_add] at hM
    exact hM
  have h3 : M 0 0 * M 1 1 + M 0 1 * M 1 0 + 1 = 0 := by
    rw [hM']
    exact CharTwo.add_self_eq_zero 1
  linear_combination h3

private theorem vecMul_pairMat_apply_inl {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] {a b : ι} (hab : a ≠ b)
    (g : Matrix (Fin 2) (Fin 2) R) (v : ι → R) :
    (v ᵥ* pairMat a b g) a = v a * g 0 0 + v b * g 1 0 := by
  rw [Matrix.vecMul_apply_eq_sum,
    Fintype.sum_eq_add a b hab (fun x hx => by
      rw [pairMat_apply_of_ne hx.1 hx.2, one_apply_ne hx.1, mul_zero])]
  obtain ⟨h1, _, h3, _⟩ := pairMat_apply_pair hab g
  rw [h1, h3]

private theorem vecMul_pairMat_apply_inr {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] {a b : ι} (hab : a ≠ b)
    (g : Matrix (Fin 2) (Fin 2) R) (v : ι → R) :
    (v ᵥ* pairMat a b g) b = v a * g 0 1 + v b * g 1 1 := by
  rw [Matrix.vecMul_apply_eq_sum,
    Fintype.sum_eq_add a b hab (fun x hx => by
      rw [pairMat_apply_of_ne hx.1 hx.2, one_apply_ne hx.2, mul_zero])]
  obtain ⟨_, h2, _, h4⟩ := pairMat_apply_pair hab g
  rw [h2, h4]

private theorem vecMul_pairMat_apply_of_notMem {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R] {a b : ι}
    (g : Matrix (Fin 2) (Fin 2) R) {r : ι} (hra : r ≠ a) (hrb : r ≠ b) (v : ι → R) :
    (v ᵥ* pairMat a b g) r = v r := by
  rw [Matrix.vecMul_apply_eq_sum]
  rw [Finset.sum_eq_single r]
  · rw [pairMat_apply_of_ne' hra hrb, one_apply_eq, mul_one]
  · intro x _ hxr
    rw [pairMat_apply_of_ne' hra hrb, one_apply_ne hxr, mul_zero]
  · simp

private theorem eq_zero_of_vecMul_sub_one_eq_zero [CharP F 2]
    {g : SpecialLinearGroup (Fin 2) F} (htr : (g : Matrix (Fin 2) (Fin 2) F).trace ≠ 0)
    {x : Fin 2 → F} (hx : x ᵥ* ((g : Matrix (Fin 2) (Fin 2) F) - 1) = 0) : x = 0 :=
  Matrix.eq_zero_of_vecMul_eq_zero (by
    rw [det_sub_one_eq_trace _ (Matrix.SpecialLinearGroup.det_coe g)]
    exact htr) hx

private theorem eq_zero_of_mulVec_sub_one_eq_zero [CharP F 2]
    {g : SpecialLinearGroup (Fin 2) F} (htr : (g : Matrix (Fin 2) (Fin 2) F).trace ≠ 0)
    {y : Fin 2 → F} (hy : ((g : Matrix (Fin 2) (Fin 2) F) - 1) *ᵥ y = 0) : y = 0 :=
  Matrix.eq_zero_of_mulVec_eq_zero (by
    rw [det_sub_one_eq_trace _ (Matrix.SpecialLinearGroup.det_coe g)]
    exact htr) hy

private theorem eq_zero_pair_of_fixed_left [CharP F 2] {g : SpecialLinearGroup (Fin 2) F}
    (htr : (g : Matrix (Fin 2) (Fin 2) F).trace ≠ 0) {x₀ x₁ : F}
    (h₀ : x₀ * (g : Matrix (Fin 2) (Fin 2) F) 0 0 + x₁ * (g : Matrix (Fin 2) (Fin 2) F) 1 0 = x₀)
    (h₁ : x₀ * (g : Matrix (Fin 2) (Fin 2) F) 0 1 + x₁ * (g : Matrix (Fin 2) (Fin 2) F) 1 1 = x₁) :
    x₀ = 0 ∧ x₁ = 0 := by
  have hx : (![x₀, x₁] : Fin 2 → F) ᵥ* ((g : Matrix (Fin 2) (Fin 2) F) - 1) = 0 := by
    rw [funext_iff, Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · rw [Pi.zero_apply, Matrix.vecMul_apply_eq_sum, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.sub_apply,
        Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
        Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero]
      rw [CharTwo.sub_eq_add, mul_add, mul_one, add_right_comm, h₀]
      exact CharTwo.add_self_eq_zero _
    · rw [Pi.zero_apply, Matrix.vecMul_apply_eq_sum, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.sub_apply,
        Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
        Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero]
      rw [CharTwo.sub_eq_add, mul_add, mul_one, ← add_assoc, h₁]
      exact CharTwo.add_self_eq_zero _
  have hzero := eq_zero_of_vecMul_sub_one_eq_zero htr hx
  exact ⟨by simpa using congrFun hzero 0, by simpa using congrFun hzero 1⟩

private theorem eq_zero_pair_of_fixed_right [CharP F 2] {g : SpecialLinearGroup (Fin 2) F}
    (htr : (g : Matrix (Fin 2) (Fin 2) F).trace ≠ 0) {y₀ y₁ : F}
    (h₀ : y₀ = (g : Matrix (Fin 2) (Fin 2) F) 0 0 * y₀ + (g : Matrix (Fin 2) (Fin 2) F) 0 1 * y₁)
    (h₁ : y₁ = (g : Matrix (Fin 2) (Fin 2) F) 1 0 * y₀ + (g : Matrix (Fin 2) (Fin 2) F) 1 1 * y₁) :
    y₀ = 0 ∧ y₁ = 0 := by
  have hy : ((g : Matrix (Fin 2) (Fin 2) F) - 1) *ᵥ (![y₀, y₁] : Fin 2 → F) = 0 := by
    rw [funext_iff, Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · rw [Pi.zero_apply, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.sub_apply,
        Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
        Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero]
      rw [CharTwo.sub_eq_add, add_mul, one_mul, add_right_comm, ← h₀]
      exact CharTwo.add_self_eq_zero _
    · rw [Pi.zero_apply, Matrix.mulVec_apply_eq_sum, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.sub_apply,
        Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
        Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero]
      rw [CharTwo.sub_eq_add, add_mul, one_mul, ← add_assoc, ← h₁]
      exact CharTwo.add_self_eq_zero _
  have hzero := eq_zero_of_mulVec_sub_one_eq_zero htr hy
  exact ⟨by simpa using congrFun hzero 0, by simpa using congrFun hzero 1⟩

theorem trace_ne_zero_of_pow_eq_one [CharP F 2] {g : SpecialLinearGroup (Fin 2) F} (hg : g ≠ 1)
    {p : ℕ} (hp : Odd p) (hgp : g ^ p = 1) :
    (g : Matrix (Fin 2) (Fin 2) F).trace ≠ 0 := by
  intro hzero
  have htr : (g : Matrix (Fin 2) (Fin 2) F).trace = 0 := hzero
  have hdet : (g : Matrix (Fin 2) (Fin 2) F).det = 1 := Matrix.SpecialLinearGroup.det_coe g
  have htr' : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = (g : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    rw [Matrix.trace_fin_two] at htr
    exact CharTwo.add_eq_zero.mp htr
  have hdet' : (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 0 0 +
      (g : Matrix (Fin 2) (Fin 2) F) 0 1 * (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
    rw [Matrix.det_fin_two] at hdet
    rw [← htr'] at hdet
    rwa [CharTwo.sub_eq_add] at hdet
  have hMM : (g : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) = 1 := by
    have h00 : ((g : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F)) 0 0 = (1 : Matrix (Fin 2) (Fin 2) F) 0 0 := by
      rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq]
      exact hdet'
    have h01 : ((g : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F)) 0 1 = (1 : Matrix (Fin 2) (Fin 2) F) 0 1 := by
      rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
        ← htr', mul_comm ((g : Matrix (Fin 2) (Fin 2) F) 0 0) ((g : Matrix (Fin 2) (Fin 2) F) 0 1)]
      exact CharTwo.add_self_eq_zero _
    have h10 : ((g : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F)) 1 0 = (1 : Matrix (Fin 2) (Fin 2) F) 1 0 := by
      rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0),
        ← htr', mul_comm ((g : Matrix (Fin 2) (Fin 2) F) 1 0) ((g : Matrix (Fin 2) (Fin 2) F) 0 0)]
      exact CharTwo.add_self_eq_zero _
    have h11 : ((g : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F)) 1 1 = (1 : Matrix (Fin 2) (Fin 2) F) 1 1 := by
      rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq, ← htr',
        mul_comm ((g : Matrix (Fin 2) (Fin 2) F) 1 0) ((g : Matrix (Fin 2) (Fin 2) F) 0 1),
        add_comm, hdet']
    rw [← Matrix.ext_iff, Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · rw [Fin.forall_fin_two]
      exact ⟨h00, h01⟩
    · rw [Fin.forall_fin_two]
      exact ⟨h10, h11⟩
  have hg2 : g ^ 2 = 1 := by
    apply Subtype.ext
    rw [pow_two, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    exact hMM
  obtain ⟨k, rfl⟩ := hp
  have hgn : g ^ (2 * k + 1) = g := by
    rw [pow_succ, pow_mul, hg2, one_pow, one_mul]
  rw [hgn] at hgp
  exact hg hgp

theorem commute_of_commute_of_trace_ne_zero [CharP F 2] {g h h' : SpecialLinearGroup (Fin 2) F}
    (htr : (g : Matrix (Fin 2) (Fin 2) F).trace ≠ 0) (hh : h * g = g * h) (hh' : h' * g = g * h') :
    h * h' = h' * h := by
  let M : Matrix (Fin 2) (Fin 2) F := (g : Matrix (Fin 2) (Fin 2) F)
  let N : Matrix (Fin 2) (Fin 2) F := (h : Matrix (Fin 2) (Fin 2) F)
  let N' : Matrix (Fin 2) (Fin 2) F := (h' : Matrix (Fin 2) (Fin 2) F)
  let κ : F := M 0 0 + M 1 1
  let t : F := N 0 0 + N 1 1
  let t' : F := N' 0 0 + N' 1 1
  have hκ : κ ≠ 0 := by
    dsimp only [κ]
    rw [Matrix.trace_fin_two] at htr
    exact htr
  have hMN : N * M = M * N := by
    have := congrArg (fun x : SpecialLinearGroup (Fin 2) F => (x : Matrix (Fin 2) (Fin 2) F)) hh
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at this
    exact this
  have hMN' : N' * M = M * N' := by
    have := congrArg (fun x : SpecialLinearGroup (Fin 2) F => (x : Matrix (Fin 2) (Fin 2) F)) hh'
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul] at this
    exact this
  have hE2 : N 0 1 * κ = M 0 1 * t := by
    have e01 : N 0 0 * M 0 1 + N 0 1 * M 1 1 = M 0 0 * N 0 1 + M 0 1 * N 1 1 := by
      have := congrFun (congrFun hMN 0) 1
      simpa only [Matrix.mul_apply, Fin.sum_univ_two] using this
    have h : N 0 1 * (M 1 1 - M 0 0) = M 0 1 * (N 1 1 - N 0 0) := by
      linear_combination e01
    rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add, add_comm (M 1 1) (M 0 0),
      add_comm (N 1 1) (N 0 0)] at h
    exact h
  have hE3 : N 1 0 * κ = M 1 0 * t := by
    have e10 : N 1 0 * M 0 0 + N 1 1 * M 1 0 = M 1 0 * N 0 0 + M 1 1 * N 1 0 := by
      have := congrFun (congrFun hMN 1) 0
      simpa only [Matrix.mul_apply, Fin.sum_univ_two] using this
    have h : N 1 0 * (M 0 0 - M 1 1) = M 1 0 * (N 0 0 - N 1 1) := by
      linear_combination e10
    rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add] at h
    exact h
  have hE2' : N' 0 1 * κ = M 0 1 * t' := by
    have e01 : N' 0 0 * M 0 1 + N' 0 1 * M 1 1 = M 0 0 * N' 0 1 + M 0 1 * N' 1 1 := by
      have := congrFun (congrFun hMN' 0) 1
      simpa only [Matrix.mul_apply, Fin.sum_univ_two] using this
    have h : N' 0 1 * (M 1 1 - M 0 0) = M 0 1 * (N' 1 1 - N' 0 0) := by
      linear_combination e01
    rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add, add_comm (M 1 1) (M 0 0),
      add_comm (N' 1 1) (N' 0 0)] at h
    exact h
  have hE3' : N' 1 0 * κ = M 1 0 * t' := by
    have e10 : N' 1 0 * M 0 0 + N' 1 1 * M 1 0 = M 1 0 * N' 0 0 + M 1 1 * N' 1 0 := by
      have := congrFun (congrFun hMN' 1) 0
      simpa only [Matrix.mul_apply, Fin.sum_univ_two] using this
    have h : N' 1 0 * (M 0 0 - M 1 1) = M 1 0 * (N' 0 0 - N' 1 1) := by
      linear_combination e10
    rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add] at h
    exact h
  have hZ : N 0 0 * t' + t * N' 1 1 = N' 0 0 * t + t' * N 1 1 := by
    dsimp only [t, t']
    linear_combination (N 0 0 * N' 1 1 - N' 0 0 * N 1 1) * (CharTwo.two_eq_zero (R := F))
  have hkey1 : N 0 1 * N' 1 0 = N' 0 1 * N 1 0 := by
    refine mul_right_cancel₀ (mul_ne_zero hκ hκ) ?_
    calc (N 0 1 * N' 1 0) * (κ * κ)
        = (N 0 1 * κ) * (N' 1 0 * κ) := by ring
      _ = (M 0 1 * t) * (M 1 0 * t') := by rw [hE2, hE3']
      _ = (M 0 1 * t') * (M 1 0 * t) := by ring
      _ = (N' 0 1 * κ) * (N 1 0 * κ) := by rw [← hE2', ← hE3]
      _ = (N' 0 1 * N 1 0) * (κ * κ) := by ring
  have hkey2 : N 1 0 * N' 0 1 = N' 1 0 * N 0 1 := by
    refine mul_right_cancel₀ (mul_ne_zero hκ hκ) ?_
    calc (N 1 0 * N' 0 1) * (κ * κ)
        = (N 1 0 * κ) * (N' 0 1 * κ) := by ring
      _ = (M 1 0 * t) * (M 0 1 * t') := by rw [hE3, hE2']
      _ = (M 1 0 * t') * (M 0 1 * t) := by ring
      _ = (N' 1 0 * κ) * (N 0 1 * κ) := by rw [← hE3', ← hE2]
      _ = (N' 1 0 * N 0 1) * (κ * κ) := by ring
  have hkey3 : (N 0 0 * N' 0 1 + N 0 1 * N' 1 1) * κ =
      (N' 0 0 * N 0 1 + N' 0 1 * N 1 1) * κ := by
    linear_combination (N 0 0) * hE2' + (N' 1 1) * hE2 - (N' 0 0) * hE2 -
      (N 1 1) * hE2' + (M 0 1) * hZ
  have hkey4 : (N 1 0 * N' 0 0 + N 1 1 * N' 1 0) * κ =
      (N' 1 0 * N 0 0 + N' 1 1 * N 1 0) * κ := by
    linear_combination (N' 0 0) * hE3 + (N 1 1) * hE3' - (N 0 0) * hE3' -
      (N' 1 1) * hE3 - (M 1 0) * hZ
  have hfinal : N * N' = N' * N := by
    rw [← Matrix.ext_iff, Fin.forall_fin_two]
    refine ⟨?_, ?_⟩ <;> rw [Fin.forall_fin_two] <;> refine ⟨?_, ?_⟩
    · simp only [Matrix.mul_apply, Fin.sum_univ_two]
      rw [hkey1, mul_comm (N 0 0) (N' 0 0)]
    · simp only [Matrix.mul_apply, Fin.sum_univ_two]
      exact mul_right_cancel₀ hκ hkey3
    · simp only [Matrix.mul_apply, Fin.sum_univ_two]
      exact mul_right_cancel₀ hκ hkey4
    · simp only [Matrix.mul_apply, Fin.sum_univ_two]
      rw [hkey2, mul_comm (N 1 1) (N' 1 1)]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  exact hfinal

theorem exists_lam_zero_mul_levi_of_commute [CharP F 2] {m : ℕ} {g : SpecialLinearGroup (Fin 2) F}
    (htr : (g : Matrix (Fin 2) (Fin 2) F).trace ≠ 0) {u : StatedSp (m + 1) F}
    (hu : u * lam (0 : Fin (m + 1)) g = lam (0 : Fin (m + 1)) g * u) :
    ∃ (h : SpecialLinearGroup (Fin 2) F) (s : StatedSp m F),
      u = lam (0 : Fin (m + 1)) h * CFSG.StandardType.spLeviBlock m F s ∧ h * g = g * h := by
  let M : Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) F := mat (m + 1) F u
  let Γ : Matrix (Fin (m + 1) ⊕ Fin (m + 1)) (Fin (m + 1) ⊕ Fin (m + 1)) F :=
    mat (m + 1) F (lam (0 : Fin (m + 1)) g)
  have hΓpair : Γ = pairMat (Sum.inl (0 : Fin (m + 1))) (Sum.inr (0 : Fin (m + 1)))
      (g : Matrix (Fin 2) (Fin 2) F) := by
    dsimp only [Γ]
    exact mat_lam (0 : Fin (m + 1)) g
  have hcommM : M * Γ = Γ * M := by
    have h := congrArg (mat (m + 1) F) hu
    rw [map_mul, map_mul] at h
    exact h
  have hzero_plane : Sum.inl (0 : Fin (m + 1)) ≠ Sum.inr (0 : Fin (m + 1)) := Sum.inl_ne_inr
  have row_zero : ∀ r : Fin (m + 1) ⊕ Fin (m + 1), r ≠ Sum.inl 0 → r ≠ Sum.inr 0 →
      M r (Sum.inl 0) = 0 ∧ M r (Sum.inr 0) = 0 := by
    intro r hra hrb
    have hrow : M r ᵥ* Γ = M r := by
      have h1 : M r ᵥ* Γ = (M * Γ) r := (Matrix.mul_apply_eq_vecMul M Γ r).symm
      have h3 : (Γ * M) r = M r := by
        rw [Matrix.mul_apply_eq_vecMul]
        have hΓr : Γ r = (1 : Matrix (Fin (m + 1) ⊕ Fin (m + 1))
            (Fin (m + 1) ⊕ Fin (m + 1)) F) r := by
          funext x
          rw [hΓpair]
          exact pairMat_apply_of_ne hra hrb (g : Matrix (Fin 2) (Fin 2) F) x
        rw [hΓr, ← Matrix.mul_apply_eq_vecMul, Matrix.one_mul]
      rw [h1, hcommM, h3]
    refine eq_zero_pair_of_fixed_left htr ?_ ?_
    · have h := congrFun hrow (Sum.inl 0)
      rw [hΓpair, vecMul_pairMat_apply_inl hzero_plane] at h
      exact h
    · have h := congrFun hrow (Sum.inr 0)
      rw [hΓpair, vecMul_pairMat_apply_inr hzero_plane] at h
      exact h
  have col_zero : ∀ c : Fin (m + 1) ⊕ Fin (m + 1), c ≠ Sum.inl 0 → c ≠ Sum.inr 0 →
      M (Sum.inl 0) c = 0 ∧ M (Sum.inr 0) c = 0 := by
    intro c hca hcb
    have hL : (M * Γ) (Sum.inl 0) c = M (Sum.inl 0) c := by
      rw [Matrix.mul_apply_eq_vecMul, hΓpair,
        vecMul_pairMat_apply_of_notMem (g : Matrix (Fin 2) (Fin 2) F) hca hcb]
    have hR : (Γ * M) (Sum.inl 0) c = (g : Matrix (Fin 2) (Fin 2) F) 0 0 * M (Sum.inl 0) c +
        (g : Matrix (Fin 2) (Fin 2) F) 0 1 * M (Sum.inr 0) c := by
      rw [Matrix.mul_apply_eq_vecMul, hΓpair, Matrix.vecMul_apply_eq_sum]
      rw [Fintype.sum_eq_add (Sum.inl 0) (Sum.inr 0) hzero_plane (fun x hx => by
        rw [pairMat_apply_fst_of_ne hx.1 hx.2, zero_mul])]
      obtain ⟨h1, h2, _, _⟩ := pairMat_apply_pair hzero_plane (g : Matrix (Fin 2) (Fin 2) F)
      rw [h1, h2]
    have hL' : (M * Γ) (Sum.inr 0) c = M (Sum.inr 0) c := by
      rw [Matrix.mul_apply_eq_vecMul, hΓpair,
        vecMul_pairMat_apply_of_notMem (g : Matrix (Fin 2) (Fin 2) F) hca hcb]
    have hR' : (Γ * M) (Sum.inr 0) c = (g : Matrix (Fin 2) (Fin 2) F) 1 0 * M (Sum.inl 0) c +
        (g : Matrix (Fin 2) (Fin 2) F) 1 1 * M (Sum.inr 0) c := by
      rw [Matrix.mul_apply_eq_vecMul, hΓpair, Matrix.vecMul_apply_eq_sum]
      rw [Fintype.sum_eq_add (Sum.inl 0) (Sum.inr 0) hzero_plane (fun x hx => by
        rw [pairMat_apply_snd_of_ne hzero_plane hx.1 hx.2, zero_mul])]
      obtain ⟨_, _, h3, h4⟩ := pairMat_apply_pair hzero_plane (g : Matrix (Fin 2) (Fin 2) F)
      rw [h3, h4]
    refine eq_zero_pair_of_fixed_right htr ?_ ?_
    · have h := congrFun (congrFun hcommM (Sum.inl 0)) c
      rw [hL, hR] at h
      exact h
    · have h := congrFun (congrFun hcommM (Sum.inr 0)) c
      rw [hL', hR'] at h
      exact h
  have hplane : ∀ j : Fin m, Sum.inl j.succ ≠ (Sum.inl (0 : Fin (m + 1)) :
      Fin (m + 1) ⊕ Fin (m + 1)) := fun j => fun h => Fin.succ_ne_zero j (Sum.inl_injective h)
  have hplane' : ∀ j : Fin m, Sum.inr j.succ ≠ (Sum.inl (0 : Fin (m + 1)) :
      Fin (m + 1) ⊕ Fin (m + 1)) := fun _ => Sum.inr_ne_inl
  have hplane'' : ∀ j : Fin m, Sum.inl j.succ ≠ (Sum.inr (0 : Fin (m + 1)) :
      Fin (m + 1) ⊕ Fin (m + 1)) := fun _ => Sum.inl_ne_inr
  have hplane''' : ∀ j : Fin m, Sum.inr j.succ ≠ (Sum.inr (0 : Fin (m + 1)) :
      Fin (m + 1) ⊕ Fin (m + 1)) := fun j => fun h => Fin.succ_ne_zero j (Sum.inr_injective h)
  obtain ⟨h, s, hus⟩ := exists_lam_mul_levi_of_entries_zero (fun j a ha => by
    rcases ha with rfl | rfl
    · exact ⟨(row_zero (Sum.inl j.succ) (hplane j) (hplane'' j)).1,
        (row_zero (Sum.inr j.succ) (hplane' j) (hplane''' j)).1,
        (col_zero (Sum.inl j.succ) (hplane j) (hplane'' j)).1,
        (col_zero (Sum.inr j.succ) (hplane' j) (hplane''' j)).1⟩
    · exact ⟨(row_zero (Sum.inl j.succ) (hplane j) (hplane'' j)).2,
        (row_zero (Sum.inr j.succ) (hplane' j) (hplane''' j)).2,
        (col_zero (Sum.inl j.succ) (hplane j) (hplane'' j)).2,
        (col_zero (Sum.inr j.succ) (hplane' j) (hplane''' j)).2⟩)
  refine ⟨h, s, hus, ?_⟩
  apply lam_injective (0 : Fin (m + 1))
  rw [map_mul, map_mul]
  exact mul_right_cancel (by
    calc lam (0 : Fin (m + 1)) h * lam (0 : Fin (m + 1)) g *
            CFSG.StandardType.spLeviBlock m F s
        = lam (0 : Fin (m + 1)) h * (lam (0 : Fin (m + 1)) g *
            CFSG.StandardType.spLeviBlock m F s) := by rw [mul_assoc]
      _ = lam (0 : Fin (m + 1)) h * (CFSG.StandardType.spLeviBlock m F s *
            lam (0 : Fin (m + 1)) g) := by
            rw [(lam_zero_commute_spLeviBlock g s).eq]
      _ = lam (0 : Fin (m + 1)) h * CFSG.StandardType.spLeviBlock m F s *
            lam (0 : Fin (m + 1)) g := by rw [← mul_assoc]
      _ = u * lam (0 : Fin (m + 1)) g := by rw [← hus]
      _ = lam (0 : Fin (m + 1)) g * u := hu
      _ = lam (0 : Fin (m + 1)) g * (lam (0 : Fin (m + 1)) h *
            CFSG.StandardType.spLeviBlock m F s) := by rw [hus]
      _ = lam (0 : Fin (m + 1)) g * lam (0 : Fin (m + 1)) h *
            CFSG.StandardType.spLeviBlock m F s := by rw [mul_assoc])

private theorem commutator_mul_mul_of_commute {G : Type*} [Group G] {z₁ z₂ l₁ l₂ : G}
    (h₁₁ : Commute z₁ l₁) (h₁₂ : Commute z₁ l₂) (h₂₁ : Commute z₂ l₁) (h₂₂ : Commute z₂ l₂)
    (hz : Commute z₁ z₂) : ⁅z₁ * l₁, z₂ * l₂⁆ = ⁅l₁, l₂⁆ := by
  have e₁ : z₁ * l₁ = l₁ * z₁ := h₁₁.eq
  have e₂ : z₂ * l₂ = l₂ * z₂ := h₂₂.eq
  rw [commutatorElement_def, commutatorElement_def, _root_.mul_inv_rev, _root_.mul_inv_rev]
  have c1 : Commute z₁ (l₁ * (z₂ * l₂) * l₁⁻¹) :=
    (h₁₁.mul_right (hz.mul_right h₁₂)).mul_right h₁₁.inv_right
  have c2 : Commute z₂ (l₁ * l₂ * l₁⁻¹ * l₂⁻¹) :=
    ((h₂₁.mul_right h₂₂).mul_right h₂₁.inv_right).mul_right h₂₂.inv_right
  calc z₁ * l₁ * (z₂ * l₂) * (l₁⁻¹ * z₁⁻¹) * (l₂⁻¹ * z₂⁻¹)
      = (z₁ * (l₁ * (z₂ * l₂) * l₁⁻¹) * z₁⁻¹) * l₂⁻¹ * z₂⁻¹ := by group
    _ = l₁ * (z₂ * l₂) * l₁⁻¹ * l₂⁻¹ * z₂⁻¹ := by rw [c1.eq, mul_inv_cancel_right]
    _ = z₂ * (l₁ * l₂ * l₁⁻¹ * l₂⁻¹) * z₂⁻¹ := by
        rw [show l₁ * (z₂ * l₂) = z₂ * (l₁ * l₂) by
          rw [← mul_assoc, ← h₂₁.eq, mul_assoc]]
        group
    _ = l₁ * l₂ * l₁⁻¹ * l₂⁻¹ := by rw [c2.eq, mul_inv_cancel_right]

theorem le_range_spLeviBlock_of_perfect_of_commute [CharP F 2] {m : ℕ}
    {g : SpecialLinearGroup (Fin 2) F} (htr : (g : Matrix (Fin 2) (Fin 2) F).trace ≠ 0)
    {J : Subgroup (StatedSp (m + 1) F)} (hperf : J ≤ ⁅J, J⁆)
    (hc : ∀ j ∈ J, j * lam (0 : Fin (m + 1)) g = lam (0 : Fin (m + 1)) g * j) :
    J ≤ (CFSG.StandardType.spLeviBlock m F).range := by
  have hcomm : ⁅J, J⁆ ≤ (CFSG.StandardType.spLeviBlock m F).range := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨h₁, s₁, rfl, hg₁⟩ := exists_lam_zero_mul_levi_of_commute htr (hc a ha)
    obtain ⟨h₂, s₂, rfl, hg₂⟩ := exists_lam_zero_mul_levi_of_commute htr (hc b hb)
    have hh : h₁ * h₂ = h₂ * h₁ := commute_of_commute_of_trace_ne_zero htr hg₁ hg₂
    have hz : Commute (lam (0 : Fin (m + 1)) h₁) (lam (0 : Fin (m + 1)) h₂) := by
      show lam (0 : Fin (m + 1)) h₁ * lam (0 : Fin (m + 1)) h₂ =
        lam (0 : Fin (m + 1)) h₂ * lam (0 : Fin (m + 1)) h₁
      rw [← map_mul, ← map_mul, hh]
    have hC : ⁅lam (0 : Fin (m + 1)) h₁ * CFSG.StandardType.spLeviBlock m F s₁,
        lam (0 : Fin (m + 1)) h₂ * CFSG.StandardType.spLeviBlock m F s₂⁆ =
        ⁅CFSG.StandardType.spLeviBlock m F s₁, CFSG.StandardType.spLeviBlock m F s₂⁆ :=
      commutator_mul_mul_of_commute (lam_zero_commute_spLeviBlock h₁ s₁)
        (lam_zero_commute_spLeviBlock h₁ s₂) (lam_zero_commute_spLeviBlock h₂ s₁)
        (lam_zero_commute_spLeviBlock h₂ s₂) hz
    rw [hC]
    refine ⟨⁅s₁, s₂⁆, ?_⟩
    simp only [commutatorElement_def, map_mul, map_inv]
  intro j hj
  exact hcomm (hperf hj)

end CFSG.StandardType.SpJoin
