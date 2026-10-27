module

public import CFSG.RankThree.PartOne.KF.BloomOmega

public section

namespace CFSG.RankThree.PartTwo.Sec20.F3L3

open Matrix CFSG.RankThree.PartOne.KFBloom CFSG.RankThree.SubgroupLists
  CFSG.RankThree.PartOne.LIT CFSG.RepresentationTheory
open scoped MatrixGroups

theorem eq_one_of_pow_three_eq_one {p : ℕ} [Fact p.Prime] (hp : p % 3 = 2) {c : ZMod p}
    (hc : c ^ 3 = 1) : c = 1 := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  have h1 := ZMod.pow_card_sub_one_eq_one hc0
  obtain ⟨m, hm⟩ : ∃ m, p - 1 = 3 * m + 1 := ⟨p / 3, by omega⟩
  rw [hm, pow_succ, pow_mul, hc, one_pow, one_mul] at h1
  exact h1

theorem eq_one_of_scalar_det {p : ℕ} [Fact p.Prime] (hp : p % 3 = 2)
    {z : GL (Fin 3) (ZMod p)} {c : ZMod p}
    (hc : (z : Matrix (Fin 3) (Fin 3) (ZMod p)) = Matrix.scalar (Fin 3) c)
    (hdet : (z : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1) : z = 1 := by
  have h3 : c ^ 3 = 1 := by
    rw [hc, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at hdet
    exact hdet
  have h1 := eq_one_of_pow_three_eq_one hp h3
  apply Units.ext
  rw [hc, h1]
  simp

private def c2 {R : Type*} [CommRing R] (Y : Matrix (Fin 3) (Fin 3) R) : R :=
  Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 + Y 0 0 * Y 2 2 - Y 0 2 * Y 2 0 + Y 1 1 * Y 2 2 -
    Y 1 2 * Y 2 1

private theorem cayley_hamilton_three {R : Type*} [CommRing R] (Y : Matrix (Fin 3) (Fin 3) R) :
    Y * Y * Y = Y.trace • (Y * Y) - c2 Y • Y + Y.det • (1 : Matrix (Fin 3) (Fin 3) R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.trace_fin_three, Matrix.det_fin_three, c2,
      Matrix.one_apply] <;> ring

private theorem two_mul_c2 {R : Type*} [CommRing R] (Y : Matrix (Fin 3) (Fin 3) R) :
    2 * c2 Y = Y.trace ^ 2 - (Y * Y).trace := by
  simp [Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three, c2]
  ring

private theorem det_smul_one_add_smul {R : Type*} [CommRing R] (c s : R)
    (E : Matrix (Fin 3) (Fin 3) R) :
    (c • (1 : Matrix (Fin 3) (Fin 3) R) + s • E).det =
      c ^ 3 + c ^ 2 * s * E.trace + c * s ^ 2 * c2 E + s ^ 3 * E.det := by
  simp [Matrix.det_fin_three, Matrix.trace_fin_three, c2, Matrix.one_apply]
  ring

private theorem order_three_data {p : ℕ} [Fact p.Prime] (hp : p % 3 = 2)
    {Y : Matrix (Fin 3) (Fin 3) (ZMod p)} (hY3 : Y * Y * Y = 1) (hY1 : Y ≠ 1)
    (hdet : Y.det = 1) : Y.trace = 0 ∧ c2 Y = 0 ∧ (Y * Y).trace = 0 := by
  have hCH := cayley_hamilton_three Y
  rw [hY3, hdet, one_smul] at hCH
  have h1 : Y.trace • (Y * Y) = c2 Y • Y := by
    have h0 : Y.trace • (Y * Y) - c2 Y • Y = 0 := by
      have := congrArg (fun X => X - 1) hCH.symm
      simpa [sub_eq_add_neg, add_assoc] using this
    exact sub_eq_zero.mp h0
  have h2 : Y.trace • Y = c2 Y • (1 : Matrix (Fin 3) (Fin 3) (ZMod p)) := by
    have h3 := congrArg (fun X => Y * Y * X) h1
    simp only [Matrix.mul_smul] at h3
    have e1 : Y * Y * (Y * Y) = Y := by
      calc Y * Y * (Y * Y) = (Y * Y * Y) * Y := by simp only [Matrix.mul_assoc]
        _ = Y := by rw [hY3, Matrix.one_mul]
    rw [e1, hY3] at h3
    exact h3
  have hT : Y.trace = 0 := by
    by_contra hT
    apply hY1
    have h4 : Y = (Y.trace⁻¹ * c2 Y) • (1 : Matrix (Fin 3) (Fin 3) (ZMod p)) := by
      have := congrArg (fun X => Y.trace⁻¹ • X) h2
      simp only [smul_smul, inv_mul_cancel₀ hT, one_smul] at this
      exact this
    have h5 : (Y.trace⁻¹ * c2 Y) ^ 3 = 1 := by
      have h6 := hY3
      rw [h4] at h6
      have h7 := congrFun (congrFun h6 0) 0
      simp [Matrix.mul_apply, Matrix.one_apply] at h7
      linear_combination h7
    have h8 := eq_one_of_pow_three_eq_one hp h5
    rw [h4, h8, one_smul]
  have hC : c2 Y = 0 := by
    have h9 := congrFun (congrFun h2 0) 0
    simp [hT, Matrix.one_apply] at h9
    exact h9.symm
  refine ⟨hT, hC, ?_⟩
  have h10 := two_mul_c2 Y
  rw [hC, hT] at h10
  linear_combination h10

private theorem two_three_ne_zero {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) :
    (2 : ZMod p) ≠ 0 ∧ (3 : ZMod p) ≠ 0 := by
  constructor
  · intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  · intro h
    have h' : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega

private theorem exists_idempotent {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) (hp : p % 3 = 2)
    {Y : Matrix (Fin 3) (Fin 3) (ZMod p)} (hY3 : Y * Y * Y = 1) (hY1 : Y ≠ 1)
    (hdet : Y.det = 1) :
    ∃ e : Matrix (Fin 3) (Fin 3) (ZMod p), e * e = e ∧ Y * e = e * Y ∧ e.trace = 1 ∧
      c2 e = 0 ∧ e.det = 0 := by
  obtain ⟨hT, hC, hT2⟩ := order_three_data hp hY3 hY1 hdet
  obtain ⟨h2, h3⟩ := two_three_ne_zero hp3
  set e : Matrix (Fin 3) (Fin 3) (ZMod p) := (3 : ZMod p)⁻¹ • (1 + Y + Y * Y) with he
  have hY4 : Y * (Y * Y * Y) = Y := by rw [hY3, Matrix.mul_one]
  have hsq : (1 + Y + Y * Y) * (1 + Y + Y * Y) = (3 : ZMod p) • (1 + Y + Y * Y) := by
    have e1 : (1 + Y + Y * Y) * (1 + Y + Y * Y) =
        (1 + Y + Y * Y) + (Y + Y * Y + Y * Y * Y) + (Y * Y + Y * Y * Y + Y * (Y * Y * Y)) := by
      noncomm_ring
    rw [e1, hY4, hY3, show (3 : ZMod p) = 1 + 1 + 1 by norm_num, add_smul, add_smul, one_smul]
    abel
  have hee : e * e = e := by
    rw [he, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hsq, smul_smul]
    congr 1
    field_simp
  have hYe : Y * e = e * Y := by
    rw [he, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    noncomm_ring
  have htr : e.trace = 1 := by
    rw [he, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_add, hT, hT2]
    simp [Matrix.trace_one]
    field_simp
  have hc2 : c2 e = 0 := by
    have h4 := two_mul_c2 e
    rw [hee, htr] at h4
    have : (2 : ZMod p) * c2 e = 0 := by rw [h4]; simp
    exact (mul_eq_zero.mp this).resolve_left h2
  have hd : e.det = 0 := by
    have hCH := cayley_hamilton_three e
    rw [hee, hee, htr, hc2] at hCH
    have h7 := congrFun (congrFun hCH 0) 0
    simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply] at h7
    linear_combination -h7
  exact ⟨e, hee, hYe, htr, hc2, hd⟩

private theorem isometry_scaling_degenerate {K : Type*} [Field K]
    {e : Matrix (Fin 3) (Fin 3) K} (hee : e * e = e) (hdet : e.det = 0) {c d : K}
    (hc : c ^ 2 ≠ 1) (hcd : c * d ≠ 1) {M : Matrix (Fin 3) (Fin 3) K} (hMt : Mᵀ = M)
    (hiso : (c • (1 - e) + d • e)ᵀ * M * (c • (1 - e) + d • e) = M) : M.det = 0 := by
  set P : Matrix (Fin 3) (Fin 3) K := 1 - e with hP
  set g : Matrix (Fin 3) (Fin 3) K := c • P + d • e with hg
  have hPP : P * P = P := by
    rw [hP]
    calc (1 - e) * (1 - e) = 1 - e - e + e * e := by noncomm_ring
      _ = 1 - e := by rw [hee]; abel
  have hPe : P * e = 0 := by
    rw [hP]
    calc (1 - e) * e = e - e * e := by noncomm_ring
      _ = 0 := by rw [hee]; abel
  have heP : e * P = 0 := by
    rw [hP]
    calc e * (1 - e) = e - e * e := by noncomm_ring
      _ = 0 := by rw [hee]; abel
  have hgP : g * P = c • P := by
    rw [hg, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, hPP, heP]
    simp
  have hge : g * e = d • e := by
    rw [hg, Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul, hPe, hee]
    simp
  have h1 : Pᵀ * M * P = (c ^ 2) • (Pᵀ * M * P) := by
    calc Pᵀ * M * P = Pᵀ * (gᵀ * M * g) * P := by rw [hiso]
      _ = (g * P)ᵀ * M * (g * P) := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (c • P)ᵀ * M * (c • P) := by rw [hgP]
      _ = (c ^ 2) • (Pᵀ * M * P) := by
          simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, sq]
  have h2 : Pᵀ * M * e = (c * d) • (Pᵀ * M * e) := by
    calc Pᵀ * M * e = Pᵀ * (gᵀ * M * g) * e := by rw [hiso]
      _ = (g * P)ᵀ * M * (g * e) := by
          simp only [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (c • P)ᵀ * M * (d • e) := by rw [hgP, hge]
      _ = (c * d) • (Pᵀ * M * e) := by
          simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
            mul_comm d c]
  have hPMP : Pᵀ * M * P = 0 := by
    have h3 : (c ^ 2 - 1) • (Pᵀ * M * P) = 0 := by
      rw [sub_smul, one_smul, ← h1, sub_self]
    exact (smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hc)
  have hPMe : Pᵀ * M * e = 0 := by
    have h3 : (c * d - 1) • (Pᵀ * M * e) = 0 := by
      rw [sub_smul, one_smul, ← h2, sub_self]
    exact (smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hcd)
  have heMP : eᵀ * M * P = 0 := by
    have := congrArg Matrix.transpose hPMe
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hMt] at this
    simpa [Matrix.mul_assoc] using this
  have hMeq : M = eᵀ * M * e := by
    have hsum : Pᵀ + eᵀ = 1 := by
      rw [hP, Matrix.transpose_sub, Matrix.transpose_one]; abel
    calc M = (Pᵀ + eᵀ) * M * (P + e) := by
          rw [hsum, show P + e = 1 by rw [hP]; abel]; simp
      _ = Pᵀ * M * P + Pᵀ * M * e + eᵀ * M * P + eᵀ * M * e := by
          simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
          abel
      _ = eᵀ * M * e := by rw [hPMP, hPMe, heMP]; simp
  have := congrArg Matrix.det hMeq
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdet] at this
  simpa using this

theorem exists_commuting_scaling {p : ℕ} [Fact p.Prime] (hp3 : 3 < p) (hp : p % 3 = 2)
    {Y : Matrix (Fin 3) (Fin 3) (ZMod p)} (hY3 : Y * Y * Y = 1) (hY1 : Y ≠ 1)
    (hdet : Y.det = 1) :
    ∃ g : Matrix (Fin 3) (Fin 3) (ZMod p), g.det = 1 ∧ Y * g = g * Y ∧
      ∀ M : Matrix (Fin 3) (Fin 3) (ZMod p), Mᵀ = M → gᵀ * M * g = M → M.det = 0 := by
  obtain ⟨e, hee, hYe, hte, hc2e, hde⟩ := exists_idempotent hp3 hp hY3 hY1 hdet
  obtain ⟨h2, h3⟩ := two_three_ne_zero hp3
  set c : ZMod p := 2 with hc
  set d : ZMod p := (c ^ 2)⁻¹ with hd
  have hc0 : c ≠ 0 := h2
  have hcd : c * d = c⁻¹ := by rw [hd]; field_simp
  have hc2 : c ^ 2 ≠ 1 := by
    intro h
    apply h3
    rw [hc] at h
    linear_combination h
  have hcd1 : c * d ≠ 1 := by
    rw [hcd]
    intro h
    have h1 : c = 1 := inv_eq_one.mp h
    apply one_ne_zero (α := ZMod p)
    rw [hc] at h1
    linear_combination h1
  have hform : c • (1 - e) + d • e = c • (1 : Matrix (Fin 3) (Fin 3) (ZMod p)) + (d - c) • e := by
    ext i j
    by_cases hij : i = j <;>
      simp [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, hij] <;>
      ring
  refine ⟨c • (1 - e) + d • e, ?_, ?_, fun M hMt hiso => ?_⟩
  · rw [hform, det_smul_one_add_smul, hte, hc2e, hde]
    rw [hd]
    field_simp
    ring
  · rw [hform, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.smul_mul, hYe, Matrix.mul_one, Matrix.one_mul]
  · exact isometry_scaling_degenerate hee hde hc2 hcd1 hMt hiso

private theorem adMat_u_mulVec {K : Type*} [Field K] (w : Fin 3 → K) :
    adMat (1 : K) 1 0 1 *ᵥ w = ![w 0 - 2 * w 1 - w 2, w 1 + w 2, w 2] := by
  ext i
  fin_cases i <;> simp [adMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

private theorem adMat_v_mulVec {K : Type*} [Field K] (w : Fin 3 → K) :
    adMat (1 : K) 0 1 1 *ᵥ w = ![w 0, -w 0 + w 1, -w 0 + 2 * w 1 + w 2] := by
  ext i
  fin_cases i <;> simp [adMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

private theorem irreducible_adMat {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    (W : Submodule K (Fin 3 → K)) (hU : ∀ w ∈ W, adMat (1 : K) 1 0 1 *ᵥ w ∈ W)
    (hV : ∀ w ∈ W, adMat (1 : K) 0 1 1 *ᵥ w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  have hNU : ∀ w ∈ W, (![-2 * w 1 - w 2, w 2, 0] : Fin 3 → K) ∈ W := by
    intro w hw
    have := W.sub_mem (hU w hw) hw
    rw [adMat_u_mulVec] at this
    convert this using 1
    ext i
    fin_cases i <;> simp <;> ring
  have hNV : ∀ w ∈ W, (![0, -w 0, -w 0 + 2 * w 1] : Fin 3 → K) ∈ W := by
    intro w hw
    have := W.sub_mem (hV w hw) hw
    rw [adMat_v_mulVec] at this
    convert this using 1
    ext i
    fin_cases i <;> simp <;> ring
  have h2' : (-2 : K) ≠ 0 := neg_ne_zero.mpr h2
  have he0 : W ≠ ⊥ → (![1, 0, 0] : Fin 3 → K) ∈ W := by
    intro hbot
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    by_cases h2w : w 2 = 0
    · by_cases h1w : w 1 = 0
      · have h0w : w 0 ≠ 0 := by
          intro h0
          apply hw0
          ext i
          fin_cases i <;> simp [h0, h1w, h2w]
        have h3 := W.smul_mem (w 0)⁻¹ hw
        convert h3 using 1
        ext i
        fin_cases i <;> simp [h1w, h2w, h0w]
      · have h3 := W.smul_mem (-2 * w 1)⁻¹ (hNU w hw)
        have hne : (-2 * w 1) ≠ 0 := mul_ne_zero h2' h1w
        convert h3 using 1
        ext i
        fin_cases i <;> simp [h2w, hne] <;> field_simp
    · have h1 := hNU _ (hNU w hw)
      have h3 := W.smul_mem (-2 * w 2)⁻¹ h1
      have hne : (-2 * w 2) ≠ 0 := mul_ne_zero h2' h2w
      convert h3 using 1
      ext i
      fin_cases i <;> simp [hne] <;> field_simp
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  · right
    have e0 := he0 hbot
    have hx := hNV _ e0
    have e2 : (![0, 0, 1] : Fin 3 → K) ∈ W := by
      have h1 := hNV _ hx
      have h3 := W.smul_mem (-2 : K)⁻¹ h1
      convert h3 using 1
      ext i
      fin_cases i <;> simp [h2'] <;> field_simp
    have e1 : (![0, 1, 0] : Fin 3 → K) ∈ W := by
      have h1 := W.add_mem hx e2
      have h3 := W.smul_mem (-1 : K) h1
      convert h3 using 1
      ext i
      fin_cases i <;> simp
    rw [eq_top_iff]
    intro w _
    have : w = w 0 • (![1, 0, 0] : Fin 3 → K) + w 1 • (![0, 1, 0] : Fin 3 → K) +
        w 2 • (![0, 0, 1] : Fin 3 → K) := by
      ext i
      fin_cases i <;> simp
    rw [this]
    exact W.add_mem (W.add_mem (W.smul_mem _ e0) (W.smul_mem _ e1)) (W.smul_mem _ e2)

theorem omegaGL_irreducible {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    {M : Matrix (Fin 3) (Fin 3) (ZMod p)} (hMt : Mᵀ = M) (hdet : M.det ≠ 0) :
    IsIrreducibleMatrixRep (omegaGL M).subtype := by
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h')
  obtain ⟨g, c, hc, hg⟩ := exists_congr_splitForm hp2 M hMt hdet
  have h1 := omegaGL_congr g M
  rw [hg, omegaGL_smul _ hc, omegaGL_splitForm_eq_range hp] at h1
  intro W hW
  let W' : Submodule (ZMod p) (Fin 3 → ZMod p) :=
    W.comap (Matrix.mulVecLin (g : Matrix (Fin 3) (Fin 3) (ZMod p)))
  have hW' : ∀ s : SL(2, ZMod p), ∀ v ∈ W',
      ((adGL s : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v ∈ W' := by
    intro s v hv
    have hs : g * adGL s * g⁻¹ ∈ omegaGL M := by
      have : adGL s ∈ (adGL (K := ZMod p)).range := ⟨s, rfl⟩
      rw [h1] at this
      exact this
    have h3 := hW ⟨_, hs⟩ ((g : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v) hv
    show (g : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ
      (((adGL s : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v) ∈ W
    have hgg : ((g⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *
        (g : Matrix (Fin 3) (Fin 3) (ZMod p)) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have e1 : (g : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ
        (((adGL s : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v) =
        (((g * adGL s * g⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p))) *ᵥ
          ((g : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v) := by
      have e2 : ((g * adGL s * g⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *
          (g : Matrix (Fin 3) (Fin 3) (ZMod p)) =
          (g : Matrix (Fin 3) (Fin 3) (ZMod p)) *
            ((adGL s : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) := by
        rw [Units.val_mul, Units.val_mul, Matrix.mul_assoc, hgg, Matrix.mul_one]
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e2]
    rw [e1]
    exact h3
  have hu : ((adGL (⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩ : SL(2, ZMod p)) :
      GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) = adMat (1 : ZMod p) 1 0 1 := rfl
  have hv : ((adGL (⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩ : SL(2, ZMod p)) :
      GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) = adMat (1 : ZMod p) 0 1 1 := rfl
  have hU : ∀ w ∈ W', adMat (1 : ZMod p) 1 0 1 *ᵥ w ∈ W' := by
    intro w hw
    have := hW' ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩ w hw
    rwa [hu] at this
  have hV : ∀ w ∈ W', adMat (1 : ZMod p) 0 1 1 *ᵥ w ∈ W' := by
    intro w hw
    have := hW' ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩ w hw
    rwa [hv] at this
  have hinv : ∀ w, (g : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ
      (((g⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ w) = w := by
    intro w
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  rcases irreducible_adMat h2 W' hU hV with h | h
  · left
    rw [eq_bot_iff]
    intro w hw
    have h4 : ((g⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ w ∈ W' := by
      show (g : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ
        (((g⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ w) ∈ W
      rw [hinv]
      exact hw
    rw [h, Submodule.mem_bot] at h4
    rw [Submodule.mem_bot]
    have := hinv w
    rw [h4, Matrix.mulVec_zero] at this
    exact this.symm
  · right
    rw [eq_top_iff]
    intro w _
    have h4 : ((g⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ w ∈ W' := by
      rw [h]; exact Submodule.mem_top
    have h5 : (g : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ
        (((g⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ w) ∈ W := h4
    rwa [hinv] at h5

end CFSG.RankThree.PartTwo.Sec20.F3L3
