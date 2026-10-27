module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution

public section

namespace CFSG.RankThree.PartTwo.Sec14.Item148Res9

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

variable {K : Type} [Field K]

theorem commute_unitriangular_eqs {M U : Matrix (Fin 3) (Fin 3) K}
    (hU : ∀ i j : Fin 3, j < i → U i j = 0) (hUd : ∀ i, U i i = 1) (hMU : M * U = U * M) :
    U 0 1 * M 1 0 + U 0 2 * M 2 0 = 0 ∧
    U 0 1 * M 0 0 = U 0 1 * M 1 1 + U 0 2 * M 2 1 ∧
    U 0 2 * M 0 0 + U 1 2 * M 0 1 = U 0 1 * M 1 2 + U 0 2 * M 2 2 ∧
    U 1 2 * M 2 0 = 0 ∧
    U 0 1 * M 1 0 = U 1 2 * M 2 1 ∧
    U 0 2 * M 1 0 + U 1 2 * M 1 1 = U 1 2 * M 2 2 ∧
    U 0 1 * M 2 0 = 0 ∧
    U 0 2 * M 2 0 + U 1 2 * M 2 1 = 0 := by
  have h10 := hU 1 0 (by decide)
  have h20 := hU 2 0 (by decide)
  have h21 := hU 2 1 (by decide)
  have h00 := hUd 0
  have h11 := hUd 1
  have h22 := hUd 2
  have e : ∀ i j, M i 0 * U 0 j + M i 1 * U 1 j + M i 2 * U 2 j =
      U i 0 * M 0 j + U i 1 * M 1 j + U i 2 * M 2 j := fun i j => by
    have := congrFun (congrFun hMU i) j
    simpa only [Matrix.mul_apply, Fin.sum_univ_three] using this
  have e00 := e 0 0
  have e01 := e 0 1
  have e02 := e 0 2
  have e10 := e 1 0
  have e11 := e 1 1
  have e12 := e 1 2
  have e21 := e 2 1
  have e22 := e 2 2
  rw [h10, h20, h21, h00, h11, h22] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination -e00
  · linear_combination e01
  · linear_combination e02
  · linear_combination -e10
  · linear_combination e11
  · linear_combination e12
  · linear_combination e21
  · linear_combination e22

theorem eq_of_commute_unitriangular {M U V : Matrix (Fin 3) (Fin 3) K}
    (hU : ∀ i j : Fin 3, j < i → U i j = 0) (hUd : ∀ i, U i i = 1)
    (hV : ∀ i j : Fin 3, j < i → V i j = 0) (hVd : ∀ i, V i i = 1)
    (hUV : U * V ≠ V * U) (hMU : M * U = U * M) (hMV : M * V = V * M) :
    M 1 0 = 0 ∧ M 2 0 = 0 ∧ M 2 1 = 0 ∧ M 0 1 = 0 ∧ M 1 2 = 0 ∧ M 0 0 = M 1 1 ∧
      M 1 1 = M 2 2 := by
  have hD : U 0 1 * V 1 2 - V 0 1 * U 1 2 ≠ 0 := by
    intro hD
    apply hUV
    have hU10 := hU 1 0 (by decide)
    have hU20 := hU 2 0 (by decide)
    have hU21 := hU 2 1 (by decide)
    have hV10 := hV 1 0 (by decide)
    have hV20 := hV 2 0 (by decide)
    have hV21 := hV 2 1 (by decide)
    have hU00 := hUd 0
    have hU11 := hUd 1
    have hU22 := hUd 2
    have hV00 := hVd 0
    have hV11 := hVd 1
    have hV22 := hVd 2
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, hU10, hU20, hU21, hV10, hV20, hV21, hU00,
        hU11, hU22, hV00, hV11, hV22] <;> first | ring1 | linear_combination hD
  obtain ⟨a1, a2, a3, -, -, a6, -, a8⟩ := commute_unitriangular_eqs hU hUd hMU
  obtain ⟨b1, b2, b3, b4, -, b6, b7, b8⟩ := commute_unitriangular_eqs hV hVd hMV
  have cancel : ∀ x : K, (U 0 1 * V 1 2 - V 0 1 * U 1 2) * x = 0 → x = 0 := fun x hx =>
    (mul_eq_zero.mp hx).resolve_left hD
  have k20 : M 2 0 = 0 := cancel _ (by linear_combination U 0 1 * b4 - U 1 2 * b7)
  have k21 : M 2 1 = 0 := by
    have c1 : U 1 2 * M 2 1 = 0 := by linear_combination a8 - U 0 2 * k20
    have c2 : V 1 2 * M 2 1 = 0 := by linear_combination b8 - V 0 2 * k20
    exact cancel _ (by linear_combination U 0 1 * c2 - V 0 1 * c1)
  have k10 : M 1 0 = 0 := by
    have c1 : U 0 1 * M 1 0 = 0 := by linear_combination a1 - U 0 2 * k20
    have c2 : V 0 1 * M 1 0 = 0 := by linear_combination b1 - V 0 2 * k20
    exact cancel _ (by linear_combination V 1 2 * c1 - U 1 2 * c2)
  have k0011 : M 0 0 = M 1 1 := by
    have c1 : U 0 1 * (M 0 0 - M 1 1) = 0 := by linear_combination a2 + U 0 2 * k21
    have c2 : V 0 1 * (M 0 0 - M 1 1) = 0 := by linear_combination b2 + V 0 2 * k21
    have := cancel (M 0 0 - M 1 1) (by linear_combination V 1 2 * c1 - U 1 2 * c2)
    linear_combination this
  have k1122 : M 1 1 = M 2 2 := by
    have c1 : U 1 2 * (M 1 1 - M 2 2) = 0 := by linear_combination a6 - U 0 2 * k10
    have c2 : V 1 2 * (M 1 1 - M 2 2) = 0 := by linear_combination b6 - V 0 2 * k10
    have := cancel (M 1 1 - M 2 2) (by linear_combination U 0 1 * c2 - V 0 1 * c1)
    linear_combination this
  have c1 : U 1 2 * M 0 1 = U 0 1 * M 1 2 := by
    linear_combination a3 - U 0 2 * k0011 - U 0 2 * k1122
  have c2 : V 1 2 * M 0 1 = V 0 1 * M 1 2 := by
    linear_combination b3 - V 0 2 * k0011 - V 0 2 * k1122
  have k01 : M 0 1 = 0 := cancel _ (by linear_combination U 0 1 * c2 - V 0 1 * c1)
  have k12 : M 1 2 = 0 := cancel _ (by linear_combination U 1 2 * c2 - V 1 2 * c1)
  exact ⟨k10, k20, k21, k01, k12, k0011, k1122⟩

theorem pow_entries_of_eq {M : Matrix (Fin 3) (Fin 3) K}
    (h : M 1 0 = 0 ∧ M 2 0 = 0 ∧ M 2 1 = 0 ∧ M 0 1 = 0 ∧ M 1 2 = 0 ∧ M 0 0 = M 1 1 ∧
      M 1 1 = M 2 2) (k : ℕ) :
    (M ^ k) 0 0 = M 0 0 ^ k ∧ (M ^ k) 0 1 = 0 ∧
      M 0 0 * (M ^ k) 0 2 = k * M 0 0 ^ k * M 0 2 := by
  obtain ⟨h10, h20, h21, h01, h12, h0011, h1122⟩ := h
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨i1, i2, i3⟩ := ih
    rw [pow_succ]
    simp only [Matrix.mul_apply, Fin.sum_univ_three, h10, h20, h21, h01, h12, i1, i2]
    refine ⟨by ring, by ring, ?_⟩
    rw [← h1122, ← h0011]
    push_cast
    linear_combination M 0 0 * i3

theorem eq_scalar_of_pow_eq_scalar {M : Matrix (Fin 3) (Fin 3) K}
    (h : M 1 0 = 0 ∧ M 2 0 = 0 ∧ M 2 1 = 0 ∧ M 0 1 = 0 ∧ M 1 2 = 0 ∧ M 0 0 = M 1 1 ∧
      M 1 1 = M 2 2) (hm : M 0 0 ≠ 0) {n : ℕ} (hn : (n : K) ≠ 0) {c : K}
    (hc : M ^ n = scalar (Fin 3) c) : M = scalar (Fin 3) (M 0 0) := by
  obtain ⟨-, -, h3⟩ := pow_entries_of_eq h n
  have h02 : (M ^ n) 0 2 = 0 := by
    rw [hc, scalar_apply, diagonal_apply_ne _ (by decide)]
  rw [h02, mul_zero] at h3
  have ht : M 0 2 = 0 := by
    have h4 : ((n : K) * M 0 0 ^ n) * M 0 2 = 0 := h3.symm
    exact (mul_eq_zero.mp h4).resolve_left (mul_ne_zero hn (pow_ne_zero n hm))
  obtain ⟨h10, h20, h21, h01, h12, h0011, h1122⟩ := h
  ext i j
  fin_cases i <;> fin_cases j <;> simp [scalar_apply, diagonal, h10, h20, h21, h01, h12, ht,
    ← h0011, ← h1122]

theorem conjAut_toGL (G : SpecialLinearGroup (Fin 3) K) :
    conjAut 3 K (SpecialLinearGroup.toGL G) = MulAut.conj (proj 3 K G) := by
  ext x
  obtain ⟨y, rfl⟩ := proj_surjective 3 K x
  rw [conjAut_proj, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation]
  simp [SpecialLinearGroup.toGL]

theorem inv_mul_mul_pow {G : Type*} [Group G] (x y : G) (n : ℕ) :
    (x⁻¹ * y * x) ^ n = x⁻¹ * y ^ n * x := by
  have h := conj_pow (a := x⁻¹) (b := y) (i := n)
  rwa [inv_inv] at h

theorem conjAut_eq_one_of_fixes [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (h3 : (3 : K) ≠ 0)
    (B : GL (Fin 3) K) {n : ℕ} (hn : (n : K) ≠ 0) (hBn : conjAut 3 K B ^ n = 1)
    (R : Subgroup (projectiveSL 3 K)) (hR : IsPGroup p R)
    (hfix : ∀ r ∈ R, conjAut 3 K B r = r) {u v : projectiveSL 3 K} (hu : u ∈ R) (hv : v ∈ R)
    (huv : u * v ≠ v * u) : conjAut 3 K B = 1 := by
  obtain ⟨S, hRS⟩ := hR.exists_le_sylow
  obtain ⟨S0, hS0⟩ := exists_sylow_projUnitriangular (K := K) p (n := 3) (by norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (projectiveSL 3 K) S0 S
  obtain ⟨G, rfl⟩ := proj_surjective 3 K g
  set g := proj 3 K G with hgdef
  set A : GL (Fin 3) K := SpecialLinearGroup.toGL G with hA
  set B' : GL (Fin 3) K := A⁻¹ * B * A with hB'
  have hcB' : conjAut 3 K B' = (MulAut.conj g)⁻¹ * conjAut 3 K B * MulAut.conj g := by
    rw [hB', map_mul, map_mul, map_inv, hA, conjAut_toGL]
  have hmem : ∀ x ∈ R, g⁻¹ * x * g ∈ projUnitriangular 3 K := by
    intro x hx
    have hxS : x ∈ (S : Subgroup _) := hRS hx
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hxS
    rw [← hS0]
    convert hxS using 1
    rw [MulAut.smul_def, MulAut.conj_inv_apply]
  have hfix' : ∀ x ∈ R, conjAut 3 K B' (g⁻¹ * x * g) = g⁻¹ * x * g := by
    intro x hx
    rw [hcB', MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, ← mul_assoc, ← mul_assoc,
      mul_inv_cancel, one_mul, mul_assoc, mul_inv_cancel, mul_one, hfix x hx, ← map_inv,
      MulAut.conj_apply, inv_inv]
  have hlift : ∀ x ∈ R, ∃ U : SpecialLinearGroup (Fin 3) K, U ∈ unitriangular 3 K ∧
      proj 3 K U = g⁻¹ * x * g ∧
      (B' : Matrix (Fin 3) (Fin 3) K) * (U : Matrix (Fin 3) (Fin 3) K) =
        (U : Matrix (Fin 3) (Fin 3) K) * (B' : Matrix (Fin 3) (Fin 3) K) := by
    intro x hx
    obtain ⟨U, hU, hUx⟩ := hmem x hx
    refine ⟨U, hU, hUx, ?_⟩
    have h1 := hfix' x hx
    rw [← hUx, conjAut_proj, proj_eq_proj_iff] at h1
    obtain ⟨c, -, hc⟩ := h1
    set W := CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K B' U
      with hW
    have hWm : (W : Matrix (Fin 3) (Fin 3) K) = (B' : Matrix (Fin 3) (Fin 3) K) *
        (U : Matrix (Fin 3) (Fin 3) K) * ((B'⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
      coe_slConjugation B' U
    have hc' : ((W⁻¹ * U : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        scalar (Fin 3) (c : K) := hc
    have hUW : (U : Matrix (Fin 3) (Fin 3) K) = (W : Matrix (Fin 3) (Fin 3) K) *
        scalar (Fin 3) (c : K) := by
      rw [← hc', ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]
    have htrU : (U : Matrix (Fin 3) (Fin 3) K).trace = 3 := by
      rw [Matrix.trace_fin_three, hU.2 0, hU.2 1, hU.2 2]
      norm_num
    have htrW : (W : Matrix (Fin 3) (Fin 3) K).trace = (U : Matrix (Fin 3) (Fin 3) K).trace := by
      rw [hWm, Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mul]
    have hc1 : (c : K) = 1 := by
      have h2 := congrArg Matrix.trace hUW
      rw [Matrix.trace_mul_comm, scalar_apply, ← smul_eq_diagonal_mul, Matrix.trace_smul,
        htrW, htrU, smul_eq_mul] at h2
      have h4 : (3 : K) * ((c : K) - 1) = 0 := by linear_combination -h2
      have h5 := (mul_eq_zero.mp h4).resolve_left h3
      linear_combination h5
    rw [hc1, map_one, Matrix.mul_one, hWm] at hUW
    calc (B' : Matrix (Fin 3) (Fin 3) K) * (U : Matrix (Fin 3) (Fin 3) K) =
        (B' : Matrix (Fin 3) (Fin 3) K) * (U : Matrix (Fin 3) (Fin 3) K) *
          (((B'⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            (B' : Matrix (Fin 3) (Fin 3) K)) := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
      _ = (U : Matrix (Fin 3) (Fin 3) K) * (B' : Matrix (Fin 3) (Fin 3) K) := by
          rw [← Matrix.mul_assoc, ← hUW]
  obtain ⟨U, hU, hUu, hBU⟩ := hlift u hu
  obtain ⟨V, hV, hVv, hBV⟩ := hlift v hv
  have hUV : (U : Matrix (Fin 3) (Fin 3) K) * (V : Matrix (Fin 3) (Fin 3) K) ≠
      (V : Matrix (Fin 3) (Fin 3) K) * (U : Matrix (Fin 3) (Fin 3) K) := by
    intro h
    apply huv
    have h1 : U * V = V * U := by
      apply Subtype.ext
      change ((U * V : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((V * U : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, h]
    have h2 := congrArg (proj 3 K) h1
    rw [map_mul, map_mul, hUu, hVv] at h2
    calc u * v = g * ((g⁻¹ * u * g) * (g⁻¹ * v * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * v * g) * (g⁻¹ * u * g)) * g⁻¹ := by rw [h2]
      _ = v * u := by group
  have hent := eq_of_commute_unitriangular (M := (B' : Matrix (Fin 3) (Fin 3) K)) hU.1 hU.2
    hV.1 hV.2 hUV hBU hBV
  have hpow : conjAut 3 K (B' ^ n) = 1 := by
    rw [map_pow, hcB', inv_mul_mul_pow, hBn, mul_one, inv_mul_cancel]
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) (B' ^ n) 1
    (by rw [map_one, mul_one, hpow])
  have hcm : (B' : Matrix (Fin 3) (Fin 3) K) ^ n = scalar (Fin 3) (c : K) := by
    rw [← Units.val_pow_eq_pow_val, ← hc, GeneralLinearGroup.coe_scalar]
  have hm : (B' : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := by
    intro h0
    have hdet := (Matrix.isUnit_iff_isUnit_det _).mp B'.isUnit
    obtain ⟨h10, h20, h21, -, -, -, -⟩ := hent
    rw [Matrix.det_fin_three, h0, h10, h20, h21] at hdet
    simp at hdet
  have hscal := eq_scalar_of_pow_eq_scalar hent hm hn hcm
  have hB'1 : conjAut 3 K B' = 1 := by
    have : B' = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 _ hm) :=
      Units.ext (by rw [GeneralLinearGroup.coe_scalar, Units.val_mk0, ← hscal])
    rw [this, conjAut_scalar]
  rw [hcB'] at hB'1
  calc conjAut 3 K B = MulAut.conj g * ((MulAut.conj g)⁻¹ * conjAut 3 K B * MulAut.conj g) *
      (MulAut.conj g)⁻¹ := by group
    _ = 1 := by rw [hB'1, mul_one, mul_inv_cancel]

end CFSG.RankThree.PartTwo.Sec14.Item148Res9
