module

public import CFSG.Quasithin.Background.HL3NineModel

public section

namespace CFSG.Quasithin

namespace H

namespace L3Nine

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix SU3 Tri
open scoped Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

@[expose] noncomputable def rk1 (n : ℕ) (v : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.vecMulVec v (conjV n v)

theorem rk1_apply (v : Fin 3 → K) (i j : Fin 3) : rk1 n v i j = v i * bar n (v j) := rfl

theorem herm_rk1 (hK : Nat.card K = (2 ^ n) ^ 2) (v : Fin 3 → K) :
    (conjM n (rk1 n v))ᵀ = rk1 n v := by
  ext i j
  simp only [conjM, transpose_apply, map_apply, rk1_apply, map_mul, bar_bar hK]
  ring

@[expose] noncomputable def pt (hK : Nat.card K = (2 ^ n) ^ 2) (v : Fin 3 → K) : HMod n K :=
  mkH (rk1 n v) (herm_rk1 hK v)

theorem mat_pt (hK : Nat.card K = (2 ^ n) ^ 2) (v : Fin 3 → K) : mat (pt hK v) = rk1 n v := rfl

theorem pt_zero (hK : Nat.card K = (2 ^ n) ^ 2) : pt hK (0 : Fin 3 → K) = 1 :=
  mat_injective (by
    ext i j
    simp [mat_pt, rk1_apply, mat_one])

theorem rhoT_pt (hK : Nat.card K = (2 ^ n) ^ 2) (A : GL (Fin 3) K) (v : Fin 3 → K) :
    rhoT hK A (pt hK v) = pt hK ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ v) := by
  apply mat_injective
  ext i j
  simp only [mat_rhoT, mat_pt, tw, rk1_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, transpose_apply, conjM, map_apply, map_add, map_mul]
  ring

theorem rk1_smul (v : Fin 3 → K) (c : K) : rk1 n (c • v) = (c * bar n c) • rk1 n v := by
  ext i j
  simp only [rk1_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, map_mul]
  ring

theorem eq_smul_of_rk1_eq {v w : Fin 3 → K} (hw : w ≠ 0) (h : rk1 n v = rk1 n w) :
    ∃ μ : K, v = μ • w := by
  obtain ⟨l, hl⟩ : ∃ l, w l ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hw (funext hcon)
  have hll := congrFun (congrFun h l) l
  rw [rk1_apply, rk1_apply] at hll
  have hbw : bar n (w l) ≠ 0 := (map_ne_zero (bar n)).mpr hl
  have hvl : v l ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hll
    exact mul_ne_zero hl hbw hll.symm
  have hbv : bar n (v l) ≠ 0 := (map_ne_zero (bar n)).mpr hvl
  refine ⟨bar n (w l) / bar n (v l), funext fun k => ?_⟩
  have hk := congrFun (congrFun h k) l
  rw [rk1_apply, rk1_apply] at hk
  rw [Pi.smul_apply, smul_eq_mul]
  field_simp
  linear_combination hk

omit [Finite K] in
theorem exists_det_one_mulVec {v : Fin 3 → K} (hv : v ≠ 0) :
    ∃ g : GL (Fin 3) K, (g : Matrix (Fin 3) (Fin 3) K).det = 1 ∧
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 0 1 = v := by
  by_cases h0 : v 0 ≠ 0
  · let M : Matrix (Fin 3) (Fin 3) K := !![v 0, 0, 0; v 1, (v 0)⁻¹, 0; v 2, 0, 1]
    have hM : M.det = 1 := by simp [M, Matrix.det_fin_three, h0]
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hM]; exact one_ne_zero), hM, ?_⟩
    ext i
    fin_cases i <;> simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  push Not at h0
  by_cases h1 : v 1 ≠ 0
  · let M : Matrix (Fin 3) (Fin 3) K := !![v 0, 1, 0; v 1, 0, 0; v 2, 0, (v 1)⁻¹]
    have hM : M.det = 1 := by
      simp [M, Matrix.det_fin_three, h1]
      exact neg_one_eq_one
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hM]; exact one_ne_zero), hM, ?_⟩
    ext i
    fin_cases i <;> simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  push Not at h1
  have h2 : v 2 ≠ 0 := by
    intro h2
    apply hv
    ext i
    fin_cases i <;> simp [h0, h1, h2]
  let M : Matrix (Fin 3) (Fin 3) K := !![v 0, (v 2)⁻¹, 0; v 1, 0, 1; v 2, 0, 0]
  have hM : M.det = 1 := by simp [M, Matrix.det_fin_three, h2]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hM]; exact one_ne_zero), hM, ?_⟩
  ext i
  fin_cases i <;> simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

noncomputable abbrev e00 (hK : Nat.card K = (2 ^ n) ^ 2) : HMod n K := pt hK (Pi.single 0 1)

theorem pt_eq_rhoT_e00 (hK : Nat.card K = (2 ^ n) ^ 2) (g : GL (Fin 3) K) :
    rhoT hK g (e00 hK) = pt hK ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single 0 1) :=
  rhoT_pt hK g _

theorem exists_eq_pts (hK : Nat.card K = (2 ^ n) ^ 2) (X : HMod n K) :
    ∃ l₀ l₁ l₂ : K, X = pt hK (l₀ • Pi.single 0 1) * pt hK (l₁ • Pi.single 1 1) *
      pt hK (l₂ • Pi.single 2 1) *
      (pt hK (Pi.single 0 1 + bar n (mat X 0 1) • Pi.single 1 1) * (pt hK (Pi.single 0 1))⁻¹ *
        (pt hK (bar n (mat X 0 1) • Pi.single 1 1))⁻¹) *
      (pt hK (Pi.single 0 1 + bar n (mat X 0 2) • Pi.single 2 1) * (pt hK (Pi.single 0 1))⁻¹ *
        (pt hK (bar n (mat X 0 2) • Pi.single 2 1))⁻¹) *
      (pt hK (Pi.single 1 1 + bar n (mat X 1 2) • Pi.single 2 1) * (pt hK (Pi.single 1 1))⁻¹ *
        (pt hK (bar n (mat X 1 2) • Pi.single 2 1))⁻¹) := by
  have hnorm : ∀ i : Fin 3, ∃ l : K, l * bar n l = mat X i i := by
    intro i
    by_cases h0 : mat X i i = 0
    · exact ⟨0, by rw [h0, zero_mul]⟩
    · obtain ⟨l, hl⟩ := exists_norm_eq hK (herm_apply X i i) h0
      exact ⟨l, hl⟩
  obtain ⟨l₀, hl₀⟩ := hnorm 0
  obtain ⟨l₁, hl₁⟩ := hnorm 1
  obtain ⟨l₂, hl₂⟩ := hnorm 2
  refine ⟨l₀, l₁, l₂, mat_injective ?_⟩
  have h10 := herm_apply X 1 0
  have h20 := herm_apply X 2 0
  have h21 := herm_apply X 2 1
  have h01 := herm_apply X 0 1
  have h02 := herm_apply X 0 2
  have h12 := herm_apply X 1 2
  simp only [mat_mul, mat_inv, mat_pt]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rk1_apply, hl₀, hl₁, hl₂, h10, h20, h21, h01, h02, h12]

theorem eq_zero_of_trace (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {x : K}
    (h : ∀ a : K, a * x + bar n (a * x) = 0) : x = 0 := by
  by_contra hx
  obtain ⟨z, hz⟩ := exists_bar_ne hn hK
  have h1 := h (z * x⁻¹)
  rw [mul_assoc, inv_mul_cancel₀ hx, mul_one] at h1
  apply hz
  have : bar n z = -z := eq_neg_of_add_eq_zero_right h1
  rw [this, CharTwo.neg_eq]

theorem eq_zero_of_fix (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {X : HMod n K}
    (h1 : ∀ a : K, rhoT hK (trGL (0 : Fin 3) 1 (by decide) a) X = X)
    (h2 : ∀ a : K, rhoT hK (trGL (0 : Fin 3) 2 (by decide) a) X = X) :
    ∀ i j : Fin 3, ¬ (i = 0 ∧ j = 0) → mat X i j = 0 := by
  have e1 : ∀ a : K, ∀ i j : Fin 3, mat (rhoT hK (trGL (0 : Fin 3) 1 (by decide) a) X) i j =
      mat X i j := fun a i j => by rw [h1 a]
  have e2 : ∀ a : K, ∀ i j : Fin 3, mat (rhoT hK (trGL (0 : Fin 3) 2 (by decide) a) X) i j =
      mat X i j := fun a i j => by rw [h2 a]
  simp only [mat_rhoT, tw, coe_trGL, Matrix.mul_apply, Fin.sum_univ_three, transpose_apply,
    conjM, map_apply] at e1 e2
  have h10 := herm_apply X 1 0
  have h20 := herm_apply X 2 0
  have h21 := herm_apply X 2 1
  have x11 : mat X 1 1 = 0 := by
    have := e1 1 0 1
    simp [transvection] at this
    exact this
  have x12 : mat X 1 2 = 0 := by
    have := e1 1 0 2
    simp [transvection] at this
    exact this
  have x22 : mat X 2 2 = 0 := by
    have := e2 1 0 2
    simp [transvection] at this
    exact this
  have x21 : mat X 2 1 = 0 := by
    have := e2 1 0 1
    simp [transvection] at this
    exact this
  have x10 : mat X 1 0 = 0 := by
    refine eq_zero_of_trace hn hK fun a => ?_
    have := e1 a 0 0
    simp [transvection, x11] at this
    rw [map_mul, herm_apply X 0 1]
    linear_combination this
  have x20 : mat X 2 0 = 0 := by
    refine eq_zero_of_trace hn hK fun a => ?_
    have := e2 a 0 0
    simp [transvection, x22] at this
    rw [map_mul, herm_apply X 0 2]
    linear_combination this
  have x01 : mat X 0 1 = 0 := by rw [← herm_apply, x10, map_zero]
  have x02 : mat X 0 2 = 0 := by rw [← herm_apply, x20, map_zero]
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact absurd ⟨rfl, rfl⟩ hij | assumption

omit [Finite K] [CharP K 2] in
theorem scalGL_comm (l : Kˣ) (g : GL (Fin 3) K) : scalGL l * g = g * scalGL l :=
  Units.ext (by
    rw [Units.val_mul, Units.val_mul, coe_scalGL, Matrix.smul_mul, Matrix.mul_smul, one_mul,
      mul_one])

theorem rhoT_trGL_e00 (hK : Nat.card K = (2 ^ n) ^ 2) {j : Fin 3} (hj : (0 : Fin 3) ≠ j)
    (a : K) : rhoT hK (trGL (0 : Fin 3) j hj a) (e00 hK) = e00 hK := by
  rw [pt_eq_rhoT_e00, coe_trGL]
  congr 1
  ext i
  fin_cases i <;> simp [transvection, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
    Matrix.one_apply, Matrix.single_apply, Ne.symm hj]

omit [Finite K] [CharP K 2] in
theorem det_trGL {i j : Fin 3} (hij : i ≠ j) (a : K) :
    ((trGL i j hij a : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  rw [coe_trGL]
  exact Matrix.det_transvection_of_ne i j hij a

theorem exists_scalGL_of_commute (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {f : MulAut (HMod n K)}
    (hf : ∀ g : GL (Fin 3) K, (g : Matrix (Fin 3) (Fin 3) K).det = 1 →
      f * rhoT hK g = rhoT hK g * f) :
    ∃ l : Kˣ, f = rhoT hK (scalGL l) := by
  have hcomm : ∀ g : GL (Fin 3) K, (g : Matrix (Fin 3) (Fin 3) K).det = 1 → ∀ X,
      f (rhoT hK g X) = rhoT hK g (f X) := fun g hg X => by
    rw [← MulAut.mul_apply, hf g hg, MulAut.mul_apply]
  have hfix : ∀ i j : Fin 3, ¬ (i = 0 ∧ j = 0) → mat (f (e00 hK)) i j = 0 := by
    refine eq_zero_of_fix hn hK (fun a => ?_) (fun a => ?_)
    · rw [← hcomm _ (det_trGL _ a), rhoT_trGL_e00]
    · rw [← hcomm _ (det_trGL _ a), rhoT_trGL_e00]
  set c := mat (f (e00 hK)) 0 0 with hc
  have hcbar : bar n c = c := herm_apply _ 0 0
  have hfe : mat (f (e00 hK)) = c • rk1 n (Pi.single 0 1) := by
    ext i j
    by_cases hij : i = 0 ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := hij
      simp [rk1_apply, ← hc]
    · rw [hfix i j hij]
      have : rk1 n (Pi.single (0 : Fin 3) (1 : K)) i j = 0 := by
        fin_cases i <;> fin_cases j <;> simp_all [rk1_apply]
      rw [Matrix.smul_apply, this, smul_zero]
  have hc0 : c ≠ 0 := by
    intro h0
    have h1 : f (e00 hK) = 1 := mat_injective (by rw [hfe, h0, zero_smul, mat_one])
    have h2 : e00 hK = (1 : HMod n K) := by
      rw [← map_one f] at h1
      exact f.injective h1
    have h3 := congrArg (fun Y : HMod n K => mat Y 0 0) h2
    simp [mat_pt, rk1_apply, mat_one] at h3
  obtain ⟨l, hl⟩ := exists_norm_eq hK hcbar hc0
  refine ⟨l, ?_⟩
  have hS : ∀ g : GL (Fin 3) K, Commute (rhoT hK (scalGL l)) (rhoT hK g) := fun g => by
    show rhoT hK (scalGL l) * rhoT hK g = rhoT hK g * rhoT hK (scalGL l)
    rw [← map_mul, ← map_mul, scalGL_comm]
  set f' := (rhoT hK (scalGL l))⁻¹ * f with hf'
  have hf'comm : ∀ g : GL (Fin 3) K, (g : Matrix (Fin 3) (Fin 3) K).det = 1 →
      f' * rhoT hK g = rhoT hK g * f' := by
    intro g hg
    rw [hf', mul_assoc, hf g hg, ← mul_assoc, ((hS g).inv_left).eq, mul_assoc]
  have hSe : rhoT hK (scalGL l) (e00 hK) = f (e00 hK) :=
    mat_injective (by rw [mat_rhoT_scalGL, hl, hfe]; rfl)
  have hf'e : f' (e00 hK) = e00 hK := by
    show (rhoT hK (scalGL l))⁻¹ (f (e00 hK)) = e00 hK
    rw [← hSe, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  have hf'pt : ∀ v, f' (pt hK v) = pt hK v := by
    intro v
    by_cases hv : v = 0
    · rw [hv, pt_zero, map_one]
    obtain ⟨g, hg1, hgv⟩ := exists_det_one_mulVec hv
    rw [← hgv, ← pt_eq_rhoT_e00, ← MulAut.mul_apply, hf'comm g hg1, MulAut.mul_apply, hf'e]
  have hf'1 : f' = 1 := MulEquiv.ext fun X => by
    obtain ⟨l₀, l₁, l₂, hX⟩ := exists_eq_pts hK X
    rw [MulAut.one_apply]
    conv_lhs => rw [hX]
    simp only [map_mul, map_inv, hf'pt]
    exact hX.symm
  exact (inv_mul_eq_one.mp hf'1).symm

theorem rk1_map (ψ : K ≃+* K) (v : Fin 3 → K) :
    (rk1 n v).map ψ = rk1 n (fun i => ψ (v i)) := by
  ext i j
  simp [rk1_apply, bar_map]

theorem eq_one_and_scalar_of_rhoT (hK : Nat.card K = (2 ^ n) ^ 2)
    {B : GL (Fin 3) K} {c : K} {ψ : K ≃+* K}
    (h : ∀ X : HMod n K, mat (rhoT hK B X) = c • (mat X).map ψ) :
    ψ = 1 ∧ ∃ d : K, (B : Matrix (Fin 3) (Fin 3) K) = d • 1 := by
  set b := (B : Matrix (Fin 3) (Fin 3) K) with hb
  have hv : ∀ (v : Fin 3 → K) (i j : Fin 3),
      (b *ᵥ v) i * bar n ((b *ᵥ v) j) = c * (ψ (v i) * bar n (ψ (v j))) := by
    intro v i j
    have := congrFun (congrFun (h (pt hK v)) i) j
    rw [rhoT_pt, mat_pt, mat_pt, rk1_map, Matrix.smul_apply, rk1_apply, rk1_apply,
      smul_eq_mul] at this
    exact this
  have hcol : ∀ k i : Fin 3, (b *ᵥ Pi.single i 1) k = b k i := fun k i => by
    rw [Matrix.mulVec_single_one]
    rfl
  have hz : ∀ x : K, x * bar n x = 0 → x = 0 := fun x hx => by
    rcases mul_eq_zero.mp hx with h0 | h0
    · exact h0
    · exact (map_eq_zero_iff (bar n) (bar n).injective).mp h0
  have hoff : ∀ k i : Fin 3, k ≠ i → b k i = 0 := by
    intro k i hki
    apply hz
    have := hv (Pi.single i 1) k k
    rw [hcol] at this
    rw [this, Pi.single_eq_of_ne hki, map_zero, zero_mul, mul_zero]
  have hdiag : ∀ i : Fin 3, b i i * bar n (b i i) = c := by
    intro i
    have := hv (Pi.single i 1) i i
    rw [hcol, Pi.single_eq_same, map_one, map_one, mul_one, mul_one] at this
    exact this
  have hb00 : b 0 0 ≠ 0 := by
    intro h0
    have hdet : b.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp B.isUnit).ne_zero
    apply hdet
    rw [Matrix.det_fin_three, h0, hoff 1 0 (by decide), hoff 2 0 (by decide)]
    ring
  have hc0 : c ≠ 0 := by
    rw [← hdiag 0]
    exact mul_ne_zero hb00 ((map_ne_zero (bar n)).mpr hb00)
  have hpair : ∀ j : Fin 3, j ≠ 0 → ∀ a : K,
      b 0 0 * bar n (a * b j j) = c * bar n (ψ a) := by
    intro j hj a
    have := hv (Pi.single 0 1 + a • Pi.single j 1) 0 j
    have e1 : (b *ᵥ (Pi.single 0 1 + a • Pi.single j 1)) 0 = b 0 0 := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, hcol, hcol,
        hoff 0 j (Ne.symm hj), smul_zero, add_zero]
    have e2 : (b *ᵥ (Pi.single 0 1 + a • Pi.single j 1)) j = a * b j j := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, hcol, hcol,
        hoff j 0 hj, zero_add, smul_eq_mul]
    rw [e1, e2] at this
    rw [this]
    simp [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne (Ne.symm hj)]
  have hone : ∀ j : Fin 3, j ≠ 0 → b 0 0 * bar n (b j j) = c := by
    intro j hj
    have := hpair j hj 1
    rw [one_mul, map_one, map_one, mul_one] at this
    exact this
  refine ⟨?_, b 0 0, ?_⟩
  · ext a
    have h1 := hpair 1 (by decide) a
    rw [map_mul, ← mul_assoc, mul_comm (b 0 0), mul_assoc, hone 1 (by decide), mul_comm] at h1
    have h2 := mul_left_cancel₀ hc0 h1
    have h3 := congrArg (bar n) h2
    rw [bar_bar hK, bar_bar hK] at h3
    exact h3.symm
  · have heq : ∀ j : Fin 3, j ≠ 0 → b j j = b 0 0 := by
      intro j hj
      have h1 := hone j hj
      rw [← hdiag j] at h1
      have hbj : bar n (b j j) ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at h1
        exact hc0 ((hdiag j).symm.trans (by rw [h0, mul_zero]))
      exact (mul_right_cancel₀ hbj h1).symm
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases hi : i = 0
      · subst hi
        simp
      · simp [heq i hi]
    · rw [hoff i j hij, Matrix.smul_apply, Matrix.one_apply_ne hij, smul_zero]

theorem scalar_of_rhoT_eq_one (hK : Nat.card K = (2 ^ n) ^ 2)
    {B : GL (Fin 3) K} (h : rhoT hK B = 1) : ∃ d : K, (B : Matrix (Fin 3) (Fin 3) K) = d • 1 :=
  (eq_one_and_scalar_of_rhoT (c := 1) (ψ := 1) hK fun X => by
    rw [h, MulAut.one_apply, one_smul]
    ext i j
    rfl).2

theorem eq_one_of_fldAut_eq_rhoT (hK : Nat.card K = (2 ^ n) ^ 2)
    {ψ : K ≃+* K} {B : GL (Fin 3) K} (h : fldAut ψ = rhoT hK B) : ψ = 1 :=
  (eq_one_and_scalar_of_rhoT (c := 1) hK fun X => by
    rw [← h, mat_fldAut, one_smul]).1

end L3Nine

end H

end CFSG.Quasithin
