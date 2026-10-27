module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryCoverRootData

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open scoped Matrix

universe u

variable {K : Type u} [Field K]

@[expose] def unitaryCoverConjUnits (J : HermitianForm 3 K) : Kˣ ≃* Kˣ :=
  Units.mapEquiv J.conj.toMulEquiv

@[expose] def unitaryCoverScalar (J : HermitianForm 3 K) : Kˣ →* Kˣ where
  toFun k := k * (unitaryCoverConjUnits J k)⁻¹ ^ 2
  map_one' := by simp
  map_mul' k l := by simp [mul_pow, mul_comm, mul_left_comm, mul_assoc]

@[simp]
theorem unitaryCoverScalar_val (J : HermitianForm 3 K) (k : Kˣ) :
    (unitaryCoverScalar J k : K) = (k : K) * (J.conj (k : K))⁻¹ ^ 2 := by
  simp [unitaryCoverScalar, unitaryCoverConjUnits]

@[expose] def unitaryCoverScalarImage (J : HermitianForm 3 K) : Subgroup Kˣ :=
  (unitaryCoverScalar J).range

@[expose] def unitaryCoverTorus (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (hermitianTorusPSU J hJ).range

theorem unitaryCoverScalar_norm (J : HermitianForm 3 K) (k : Kˣ) :
    (unitaryCoverScalar J k : K) * J.conj (unitaryCoverScalar J k : K) =
      (J.conj (k : K))⁻¹ * (k : K)⁻¹ := by
  have hk : (k : K) ≠ 0 := Units.ne_zero k
  have hc : J.conj (k : K) ≠ 0 := (map_ne_zero J.conj).2 hk
  rw [unitaryCoverScalar_val, map_mul, map_pow, map_inv₀, J.conj_involutive]
  field_simp [hk, hc]

theorem unitaryCoverScalar_ker_eq_torus_ker (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    (unitaryCoverScalar J).ker = (hermitianTorusPSU J hJ).ker := by
  ext k
  have hk : (k : K) ≠ 0 := Units.ne_zero k
  have hc : J.conj (k : K) ≠ 0 := (map_ne_zero J.conj).2 hk
  constructor
  · intro hs
    have hs' : (k : K) * (J.conj (k : K))⁻¹ ^ 2 = 1 := by
      simpa only [unitaryCoverScalar_val, Units.val_one] using
        congrArg Units.val (MonoidHom.mem_ker.mp hs)
    have hkc : (k : K) = J.conj (k : K) ^ 2 := by
      field_simp [hc] at hs'
      exact hs'
    have hck : J.conj (k : K) = (k : K) ^ 2 := by
      have h := congrArg J.conj hkc
      rw [map_pow, J.conj_involutive] at h
      exact h
    have hkfour : (k : K) ^ 4 = (k : K) := by
      calc
        (k : K) ^ 4 = ((k : K) ^ 2) ^ 2 := by ring
        _ = J.conj (k : K) ^ 2 := by rw [← hck]
        _ = (k : K) := hkc.symm
    have hkthree : (k : K) ^ 3 = 1 := by
      apply mul_right_cancel₀ hk
      simpa only [← pow_succ, one_mul] using hkfour
    have hn : J.conj (k : K) * (k : K) = 1 := by
      rw [hck, ← pow_succ, hkthree]
    have hcinv : (J.conj (k : K))⁻¹ = (k : K) :=
      (eq_inv_of_mul_eq_one_right hn).symm
    have hmid : J.conj (k : K) * (k : K)⁻¹ = (k : K) := by
      rw [hck]
      field_simp [hk]
    have hscalar : hermitianTorusGL J k = Matrix.GeneralLinearGroup.scalar (Fin 3) k := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [hermitianTorusGL_val, hermitianTorusMatrix,
          Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar, hcinv, hmid]
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    rw [hermitianTorusPSU_val]
    exact Matrix.ProjGenLinGroup.mk_eq_one.mpr (by
      rw [hscalar, Matrix.GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨k, rfl⟩)
  · intro ht
    have hproj : Matrix.ProjGenLinGroup.mk (hermitianTorusGL J k) = 1 := by
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp ht)
    obtain ⟨r, hr⟩ := Matrix.GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp
      (Matrix.ProjGenLinGroup.mk_eq_one.mp hproj)
    have hdiag : (J.conj (k : K))⁻¹ = J.conj (k : K) * (k : K)⁻¹ := by
      have h0 := congrArg (fun A : Matrix (Fin 3) (Fin 3) K => A 0 0) hr
      have h1 := congrArg (fun A : Matrix (Fin 3) (Fin 3) K => A 1 1) hr
      simp only [hermitianTorusGL_val, hermitianTorusMatrix,
        Matrix.scalar] at h0 h1
      exact h0.symm.trans h1
    have hkc : (k : K) = J.conj (k : K) ^ 2 := by
      field_simp [hk, hc] at hdiag
      exact hdiag
    apply MonoidHom.mem_ker.mpr
    apply Units.ext
    change (unitaryCoverScalar J k : K) = 1
    rw [unitaryCoverScalar_val]
    field_simp [hc]
    exact hkc

@[expose] def unitaryCoverTorusScalarEquiv (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    unitaryCoverTorus J hJ ≃* unitaryCoverScalarImage J :=
  (QuotientGroup.quotientKerEquivRange (hermitianTorusPSU J hJ)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq
      (unitaryCoverScalar_ker_eq_torus_ker J hJ).symm).trans
        (QuotientGroup.quotientKerEquivRange (unitaryCoverScalar J)))

@[simp]
theorem unitaryCoverTorusScalarEquiv_apply (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (k : Kˣ) :
    unitaryCoverTorusScalarEquiv J hJ ((hermitianTorusPSU J hJ).rangeRestrict k) =
      (unitaryCoverScalar J).rangeRestrict k := by
  change ((QuotientGroup.quotientKerEquivRange (hermitianTorusPSU J hJ)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq
      (unitaryCoverScalar_ker_eq_torus_ker J hJ).symm).trans
        (QuotientGroup.quotientKerEquivRange (unitaryCoverScalar J))))
      ((hermitianTorusPSU J hJ).rangeRestrict k) = _
  have hrep : QuotientGroup.quotientKerEquivRange (hermitianTorusPSU J hJ)
      ((QuotientGroup.mk' (hermitianTorusPSU J hJ).ker) k) =
        (hermitianTorusPSU J hJ).rangeRestrict k := rfl
  rw [← hrep]
  simp only [MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply]
  simp only [QuotientGroup.mk'_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

theorem unitaryCoverTorus_nativeStructure [Finite K]
    (J : HermitianForm 3 K) (q : ℕ)
    (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Nat.card (unitaryCoverTorus J hJ) = (q ^ 2 - 1) / Nat.gcd 3 (q + 1) ∧
      IsCyclic (unitaryCoverTorus J hJ) := by
  rcases huppert_II_10_12 J q hcard hfixed hJ with
    ⟨_hpoints, _rho, _pinf, _hinj, _hnatural, _hUcard,
      ⟨_R, H, _hRle, _hHle, _hN, _hinf, _hsup, hcyc, _hRcard,
        _hcomm, _hcommcard, hHcard, _hreg, _hcoord,
        hHcoord, hHsurj⟩, _htwo, _hGcard, _hthree⟩
  have hmatrix (k : Kˣ) (M : GL (Fin 3) K)
      (hM : (M : Matrix (Fin 3) (Fin 3) K) =
        !![(J.conj (k : K))⁻¹, 0, 0;
           0, J.conj (k : K) * (k : K)⁻¹, 0;
           0, 0, (k : K)]) : M = hermitianTorusGL J k := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    rw [hM, hermitianTorusGL_val]
    rfl
  have hrange : unitaryCoverTorus J hJ = H := by
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      obtain ⟨h, M, hM, hproj⟩ := hHsurj k
      have hh : (h : ProjectiveSpecialUnitaryMatrixGroup J) = hermitianTorusPSU J hJ k := by
        apply Subtype.ext
        simpa only [hmatrix k M hM, hermitianTorusPSU_val] using hproj
      rw [← hh]
      exact h.property
    · intro hx
      obtain ⟨k, M, hM, hproj⟩ := hHcoord ⟨x, hx⟩
      refine ⟨k, ?_⟩
      apply Subtype.ext
      simpa only [hmatrix k M hM, hermitianTorusPSU_val] using hproj.symm
  rw [hrange]
  exact ⟨by simpa only [Nat.gcd_comm] using hHcard, hcyc⟩

theorem unitaryCoverScalarImage_card [Finite K]
    (J : HermitianForm 3 K) (q : ℕ)
    (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Nat.card (unitaryCoverScalarImage J) = (q ^ 2 - 1) / Nat.gcd 3 (q + 1) :=
  (Nat.card_congr (unitaryCoverTorusScalarEquiv J hJ).symm.toEquiv).trans
    (unitaryCoverTorus_nativeStructure J q hcard hfixed hJ).1

theorem unitaryCoverTorus_card_odd [Finite K] [CharP K 2]
    (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Odd (Nat.card (unitaryCoverTorus J hJ)) := by
  let q := 2 ^ f
  have hqpos : 0 < q := by positivity
  have hqeven : Even q := (by decide : Even (2 : ℕ)).pow_of_ne_zero (by omega)
  rw [(unitaryCoverTorus_nativeStructure J q hcard hfixed hJ).1]
  have hdiv : Nat.gcd 3 (q + 1) ∣ q ^ 2 - 1 := by
    rw [show q ^ 2 - 1 = (q + 1) * (q - 1) by simpa using Nat.sq_sub_sq q 1]
    exact dvd_mul_of_dvd_left (Nat.gcd_dvd_right _ _) _
  exact (Nat.Even.sub_odd (pow_pos hqpos 2)
    (hqeven.pow_of_ne_zero (by decide)) odd_one).of_dvd_nat (Nat.div_dvd_of_dvd hdiv)

theorem unitaryCoverTorus_conj_root (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (k : Kˣ) (z : hermitianUnipotentCoord J) :
    hermitianTorusPSU J hJ k * hermitianUnipotentPSU J hJ z *
      (hermitianTorusPSU J hJ k)⁻¹ =
        hermitianUnipotentPSU J hJ (hermitianTorusAction J k z) := by
  rw [hermitianTorusPSU_mul_unipotent, mul_inv_cancel_right]

theorem unitaryCoverTorus_le_normalizer (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    unitaryCoverTorus J hJ ≤ Subgroup.normalizer (unitaryCoverRoot J hJ : Set _) := by
  have hconj (k : Kˣ) (x : ProjectiveSpecialUnitaryMatrixGroup J)
      (hx : x ∈ unitaryCoverRoot J hJ) :
      hermitianTorusPSU J hJ k * x * (hermitianTorusPSU J hJ k)⁻¹ ∈
        unitaryCoverRoot J hJ := by
    obtain ⟨z, rfl⟩ := hx
    rw [unitaryCoverTorus_conj_root]
    exact ⟨hermitianTorusAction J k z, rfl⟩
  rintro t ⟨k, rfl⟩
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  constructor
  · exact hconj k x
  · intro hx
    have h := hconj k⁻¹ _ hx
    simpa only [map_inv, mul_assoc, inv_mul_cancel_left, inv_inv,
      inv_mul_cancel, mul_one] using h

theorem unitaryCoverScalarImage_exists_norm_one_ne_one [Finite K]
    (J : HermitianForm 3 K) (q : ℕ)
    (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (hq : 2 < q) :
    ∃ h : unitaryCoverScalarImage J, (h.val : K) ≠ 1 ∧
      (h.val : K) * J.conj (h.val : K) = 1 := by
  obtain ⟨k, _hkq, hkthree, _hkproj, hkconj⟩ :=
    exists_hermitian_norm_one_torus_cube_ne_one J q hcard hfixed hJ hq
  refine ⟨(unitaryCoverScalar J).rangeRestrict k, ?_, ?_⟩
  · change (unitaryCoverScalar J k : K) ≠ 1
    simpa only [unitaryCoverScalar_val, hkconj, inv_inv, ← pow_succ'] using hkthree
  · change (unitaryCoverScalar J k : K) * J.conj (unitaryCoverScalar J k : K) = 1
    rw [unitaryCoverScalar_norm, hkconj, inv_inv, mul_inv_cancel₀ (Units.ne_zero k)]

end CFSG.ShultStronglyClosedTI
