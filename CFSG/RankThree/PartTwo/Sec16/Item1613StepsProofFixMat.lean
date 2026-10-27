module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs
public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.RankThree.PartTwo.Sec4.LThreePiProj

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof1613Fix

open CFSG CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.LowTwoRank (StatedScalars)
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix (ProjGenLinGroup GeneralLinearGroup)
open scoped Matrix

variable {K : Type} [Field K]

theorem eq_one_of_conj_eq_scalar_mul_of_sq {h w : GL (Fin 3) K} {lam : Kˣ}
    (hhw : h * w * h⁻¹ = GeneralLinearGroup.scalar (Fin 3) lam * w)
    (hh2 : h ^ 2 ∈ StatedScalars (Fin 3) K) : lam = 1 := by
  have hlam3 := pow_three_eq_one_of_conj_eq_scalar_mul hhw
  obtain ⟨μ, hμ⟩ := hh2
  rw [pow_two] at hμ
  have hsc : ∀ (u : Kˣ) (A : GL (Fin 3) K),
      A * GeneralLinearGroup.scalar (Fin 3) u = GeneralLinearGroup.scalar (Fin 3) u * A :=
    fun u A => (CFSG.ClassicalGroups.UnitaryFlag.commute_scalar u A).eq
  have h2w : (h * h) * w * (h * h)⁻¹ =
      GeneralLinearGroup.scalar (Fin 3) lam * GeneralLinearGroup.scalar (Fin 3) lam * w := by
    calc (h * h) * w * (h * h)⁻¹ = h * (h * w * h⁻¹) * h⁻¹ := by group
      _ = h * (GeneralLinearGroup.scalar (Fin 3) lam * w) * h⁻¹ := by rw [hhw]
      _ = GeneralLinearGroup.scalar (Fin 3) lam * (h * w * h⁻¹) := by
          rw [← mul_assoc, hsc]
          group
      _ = GeneralLinearGroup.scalar (Fin 3) lam * GeneralLinearGroup.scalar (Fin 3) lam * w := by
          rw [hhw, ← mul_assoc]
  have h2w' : (h * h) * w * (h * h)⁻¹ = w := by
    rw [← hμ, ← hsc]
    group
  have hlam2 : GeneralLinearGroup.scalar (Fin 3) (lam * lam) = 1 := by
    have h1 := h2w.symm.trans h2w'
    rw [map_mul]
    calc GeneralLinearGroup.scalar (Fin 3) lam * GeneralLinearGroup.scalar (Fin 3) lam =
        GeneralLinearGroup.scalar (Fin 3) lam * GeneralLinearGroup.scalar (Fin 3) lam * w *
          w⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hlam2' : lam * lam = 1 := by
    have h1 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) hlam2
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.val_one,
      Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h1
    exact Units.ext (by rw [Units.val_mul, Units.val_one]; simpa using h1)
  calc lam = lam ^ 3 * (lam * lam)⁻¹ := by group
    _ = 1 := by rw [hlam3, hlam2', inv_one, one_mul]

theorem mem_statedScalars_of_commute_irred {h w : GL (Fin 3) K}
    (hirr : ∀ W : Submodule K (Fin 3 → K), (∀ v ∈ W, (w : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) →
      W = ⊥ ∨ W = ⊤)
    (hhw : h * w = w * h) (hh2 : h ^ 2 ∈ StatedScalars (Fin 3) K) :
    h ∈ StatedScalars (Fin 3) K := by
  obtain ⟨μ, hμ⟩ := hh2
  set H : Matrix (Fin 3) (Fin 3) K := (h : Matrix (Fin 3) (Fin 3) K) with hHdef
  have hH2 : H * H = (μ : K) • 1 := by
    rw [hHdef, ← Units.val_mul, ← pow_two, ← hμ, coe_scalar_eq_smul]
  have hμ0 : (μ : K) ≠ 0 := μ.ne_zero
  have hδ0 : H.det ≠ 0 :=
    (h.isUnit.map (Matrix.detMonoidHom : Matrix (Fin 3) (Fin 3) K →* K)).ne_zero
  have hδ2 : H.det * H.det = (μ : K) ^ 3 := by
    have := congrArg Matrix.det hH2
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at this
    exact this
  set ν : K := H.det / μ with hν
  have hν0 : ν ≠ 0 := div_ne_zero hδ0 hμ0
  have hν2 : ν * ν = μ := by
    rw [hν, div_mul_div_comm, hδ2]
    field_simp
  set M : Matrix (Fin 3) (Fin 3) K := ν⁻¹ • H with hM
  have hM2 : M * M = 1 := by
    rw [hM, Matrix.smul_mul, Matrix.mul_smul, hH2, smul_smul, smul_smul, ← hν2]
    rw [show ν⁻¹ * ν⁻¹ * (ν * ν) = 1 by field_simp, one_smul]
  have hwM : (w : Matrix (Fin 3) (Fin 3) K) * M = M * w := by
    rw [hM, Matrix.mul_smul, Matrix.smul_mul, hHdef, ← Units.val_mul, ← Units.val_mul, hhw]
  have hscal : ∀ a : K, a ≠ 0 → H = a • 1 → h ∈ StatedScalars (Fin 3) K := fun a ha hHa =>
    CFSG.RankThree.PartTwo.Sec4.mem_statedScalars_of_eq_smul hHa ha
  set W : Submodule K (Fin 3 → K) := LinearMap.ker (Matrix.toLin' (M - 1)) with hW
  have hmemW : ∀ v, v ∈ W ↔ M *ᵥ v = v := fun v => by
    rw [hW, LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec,
      sub_eq_zero]
  have hinv : ∀ v ∈ W, (w : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W := by
    intro v hv
    rw [hmemW] at hv ⊢
    rw [Matrix.mulVec_mulVec, ← hwM, ← Matrix.mulVec_mulVec, hv]
  have hHM : H = ν • M := by
    rw [hM, smul_smul, mul_inv_cancel₀ hν0, one_smul]
  rcases hirr W hinv with hbot | htop
  ·
    have hMn : M = -1 := by
      have hall : ∀ v : Fin 3 → K, (M + 1) *ᵥ v = 0 := by
        intro v
        have hmem : (M + 1) *ᵥ v ∈ W := by
          rw [hmemW, Matrix.mulVec_mulVec, Matrix.mul_add, hM2, Matrix.mul_one, Matrix.add_mulVec,
            Matrix.add_mulVec, Matrix.one_mulVec, add_comm]
        rw [hbot, Submodule.mem_bot] at hmem
        exact hmem
      have h0 : M + 1 = 0 := by
        apply Matrix.toLin'.injective
        refine LinearMap.ext fun v => ?_
        rw [Matrix.toLin'_apply, hall v, map_zero, LinearMap.zero_apply]
      exact eq_neg_of_add_eq_zero_left h0
    refine hscal (-ν) (neg_ne_zero.mpr hν0) ?_
    rw [hHM, hMn, smul_neg, neg_smul]
  ·
    have hM1 : M = 1 := by
      apply Matrix.toLin'.injective
      refine LinearMap.ext fun v => ?_
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.one_mulVec]
      exact (hmemW v).mp (by rw [htop]; exact Submodule.mem_top)
    exact hscal ν hν0 (by rw [hHM, hM1])

theorem mem_statedScalars_of_commute_diagTau (h2 : (2 : K) = 0) {τ : K} (hτ : τ ^ 3 = 1)
    (hτ1 : τ ≠ 1) {h : GL (Fin 3) K} (hh : h * diagTau hτ = diagTau hτ * h)
    (hh2 : h ^ 2 ∈ StatedScalars (Fin 3) K) : h ∈ StatedScalars (Fin 3) K := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hτ
    exact zero_ne_one hτ
  have hτ2 : τ ^ 2 ≠ 1 := by
    intro h1
    apply hτ1
    calc τ = τ ^ 3 / τ ^ 2 := by field_simp
      _ = 1 := by rw [hτ, h1, div_one]
  have hττ2 : τ ≠ τ ^ 2 := by
    intro h1
    apply hτ1
    have : τ * τ = τ * 1 := by rw [← sq, ← h1, mul_one]
    exact mul_left_cancel₀ hτ0 this
  obtain ⟨μ, hμ⟩ := hh2
  set H : Matrix (Fin 3) (Fin 3) K := (h : Matrix (Fin 3) (Fin 3) K) with hHdef
  have hM := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K)) hh
  simp only [Units.val_mul, coe_diagTau] at hM
  rw [← hHdef] at hM
  have ent : ∀ i j, (H * !![τ, 0, 0; 0, τ ^ 2, 0; 0, 0, 1]) i j =
      (!![τ, 0, 0; 0, τ ^ 2, 0; 0, 0, 1] * H) i j := fun i j => by rw [hM]
  have aux : ∀ {X u v : K}, u ≠ v → X * u = v * X → X = 0 := fun {X u v} huv hX => by
    have h' : X * (u - v) = 0 := by rw [mul_sub, hX, mul_comm, sub_self]
    exact (mul_eq_zero.mp h').resolve_right (sub_ne_zero.mpr huv)
  have e01 := ent 0 1
  have e02 := ent 0 2
  have e10 := ent 1 0
  have e12 := ent 1 2
  have e20 := ent 2 0
  have e21 := ent 2 1
  simp [Matrix.mul_apply, Fin.sum_univ_three] at e01 e02 e10 e12 e20 e21
  have y01 : H 0 1 = 0 := aux (Ne.symm hττ2) (by linear_combination e01)
  have y02 : H 0 2 = 0 := aux (Ne.symm hτ1) (by linear_combination e02)
  have y10 : H 1 0 = 0 := aux hττ2 (by linear_combination e10)
  have y12 : H 1 2 = 0 := aux (Ne.symm hτ2) (by linear_combination e12)
  have y20 : H 2 0 = 0 := aux hτ1 (by linear_combination e20)
  have y21 : H 2 1 = 0 := aux hτ2 (by linear_combination e21)
  have hH2 : H * H = (μ : K) • 1 := by
    rw [hHdef, ← Units.val_mul, ← pow_two, ← hμ, coe_scalar_eq_smul]
  have s00 := congrFun (congrFun hH2 0) 0
  have s11 := congrFun (congrFun hH2 1) 1
  have s22 := congrFun (congrFun hH2 2) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, y01, y02, y10, y12, y20, y21] at s00 s11 s22
  have hsq : ∀ a b : K, a * a = μ → b * b = μ → a = b := fun a b ha hb => by
    have h1 : (a - b) * (a - b) = 0 := by linear_combination ha + hb + ((μ : K) - a * b) * h2
    have := mul_self_eq_zero.mp h1
    exact sub_eq_zero.mp this
  have h01 : H 1 1 = H 0 0 := hsq _ _ s11 s00
  have h02 : H 2 2 = H 0 0 := hsq _ _ s22 s00
  have hd0 : H 0 0 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at s00
    exact μ.ne_zero s00.symm
  refine CFSG.RankThree.PartTwo.Sec4.mem_statedScalars_of_eq_smul (a := H 0 0) ?_ hd0
  rw [← hHdef]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [y01, y02, y10, y12, y20, y21, h01, h02]

theorem eq_one_of_sq_of_commute_mk {w : GL (Fin 3) K} {H : Subgroup (GL (Fin 3) K)}
    (hw : ∀ h ∈ H, h * w = w * h → h ^ 2 ∈ StatedScalars (Fin 3) K →
      h ∈ StatedScalars (Fin 3) K)
    {u : ProjGenLinGroup (Fin 3) K} (hu : u ∈ projImage H) (hu2 : u ^ 2 = 1)
    (huw : u * ProjGenLinGroup.mk w = ProjGenLinGroup.mk w * u) : u = 1 := by
  obtain ⟨h, hH, rfl⟩ := hu
  have hh2 : h ^ 2 ∈ StatedScalars (Fin 3) K := by
    rw [← mk_eq_one_iff_mem_statedScalars, map_pow]
    exact hu2
  have hcomm : h * w * h⁻¹ * w⁻¹ ∈ StatedScalars (Fin 3) K := by
    rw [← mk_eq_one_iff_mem_statedScalars]
    simp only [map_mul, map_inv]
    change ProjGenLinGroup.mk h * ProjGenLinGroup.mk w = ProjGenLinGroup.mk w *
      ProjGenLinGroup.mk h at huw
    rw [huw]
    group
  obtain ⟨lam, hlam⟩ := hcomm
  have hhw : h * w * h⁻¹ = GeneralLinearGroup.scalar (Fin 3) lam * w := by
    rw [hlam]
    group
  have hlam1 := eq_one_of_conj_eq_scalar_mul_of_sq hhw hh2
  rw [hlam1, map_one, one_mul] at hhw
  have hc : h * w = w * h := by
    calc h * w = h * w * h⁻¹ * h := by group
      _ = w * h := by rw [hhw]
  rw [mk_eq_one_iff_mem_statedScalars]
  exact hw h hH hc hh2

end CFSG.RankThree.PartTwo.Sec16.Proof1613Fix
