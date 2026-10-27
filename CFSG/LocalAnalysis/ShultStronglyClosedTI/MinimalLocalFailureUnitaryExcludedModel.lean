module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsModel
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryModelPointStructure
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphismCoord
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitarySublineAutomorphismMaps

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryExcluded

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.ShultStronglyClosedTI.TwoCoreGrowth CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
open CFSG.ShultStronglyClosedTI.UnitaryHulls CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open scoped LinearAlgebra.Projectivization

theorem mem_of_sylow_of_le_normalizer {P : Type*} [Group P] {U B : Subgroup P} (S : Sylow 2 P)
    (hS : (S : Subgroup P) = U) (hB : B ≤ Subgroup.normalizer (U : Set P)) {y : P} (hy : y ∈ B)
    {k : ℕ} (hk : y ^ 2 ^ k = 1) : y ∈ U := by
  have hzp : IsPGroup 2 (Subgroup.zpowers y) := by
    rintro ⟨_, n, rfl⟩
    refine ⟨k, Subtype.ext ?_⟩
    change (y ^ n) ^ 2 ^ k = 1
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hk,
      _root_.one_zpow]
  have hUp : IsPGroup 2 U := hS ▸ S.isPGroup'
  have hY : IsPGroup 2 (Subgroup.zpowers y ⊔ U : Subgroup P) :=
    IsPGroup.to_sup_of_normal_right' hzp hUp (Subgroup.zpowers_le.mpr (hB hy))
  have hYU : Subgroup.zpowers y ⊔ U = U := by
    rw [← hS]
    exact S.is_maximal' (hS ▸ hY) (hS ▸ le_sup_right)
  rw [← hYU]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers y)

variable {K : Type} [Field K] {J : HermitianForm 3 K} {C : Subgroup J.specialSubgroup} [C.Normal]

theorem coverToPSU_heisL (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) (z : hermitianUnipotentCoord J) :
    coverToPSU J C hJ hC (heisL J C hJ z) = hermitianUnipotentPSU J hJ z :=
  rfl

theorem ker_coverToPSU (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (hC : C ≤ scalarCenter J)
    {w : J.specialSubgroup ⧸ C} (hw : coverToPSU J C hJ hC w = 1) :
    w ∈ Subgroup.center (J.specialSubgroup ⧸ C) ∧ w ^ 3 = 1 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective C w
  have hg : g ∈ scalarCenter J := by
    rw [scalarCenter_eq_ker J hJ, MonoidHom.mem_ker]
    exact hw
  refine ⟨Subgroup.mem_center_iff.mpr fun x => ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective C x
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (scalarCenter_le_center J hg) x]
  · obtain ⟨c, hc, -, hc3⟩ := hg
    rw [← map_pow]
    convert map_one (QuotientGroup.mk' C) using 2
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hc, ← map_pow, hc3, map_one, Subgroup.coe_one,
      Units.val_one]

section Finite

variable [Finite K] [CharP K 2]

theorem mem_range_heisL_of_pow_eq_one {f : ℕ} (hf : 2 ≤ f) (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (hC : C ≤ scalarCenter J)
    {x : J.specialSubgroup ⧸ C}
    (hx : coverToPGL J C hJ hC x • unitaryCoordinatePoint (K := K) 0 = unitaryCoordinatePoint 0)
    {k : ℕ} (hk : x ^ 2 ^ k = 1) : x ∈ (heisL J C hJ).range := by
  obtain ⟨-, -, -, -, -, rho, -, -, -, -, -, -, hUB, -, -, -, -, -, ⟨S, hS⟩, -⟩ :=
    UnitaryModel.unitary_three_point_structure J f hf hcard hfixed hJ
  have hUle : (hermitianUnipotentPSU J hJ).range ≤ unitaryCoordinateStabilizer J 0 :=
    unitary_entire_root_fixes_first_coordinate J hJ
  have hBN := (Subgroup.normal_subgroupOf_iff_le_normalizer hUle).mp hUB
  have hyk : coverToPSU J C hJ hC x ^ 2 ^ k = 1 := by rw [← map_pow, hk, map_one]
  obtain ⟨z, hz⟩ := mem_of_sylow_of_le_normalizer S hS hBN (y := coverToPSU J C hJ hC x) hx hyk
  set w := x * (heisL J C hJ z)⁻¹ with hwdef
  have hw : coverToPSU J C hJ hC w = 1 := by
    rw [hwdef, map_mul, map_inv, coverToPSU_heisL, hz, mul_inv_cancel]
  obtain ⟨hwc, hw3⟩ := ker_coverToPSU hJ hC hw
  have hxw : x = w * heisL J C hJ z := by rw [hwdef, inv_mul_cancel_right]
  have hcomm : Commute w (heisL J C hJ z) := (Subgroup.mem_center_iff.mp hwc _).symm
  have hh : (heisL J C hJ z) ^ 2 ^ (k + 2) = 1 := by
    rw [pow_add, mul_comm, pow_mul, ← map_pow, show (2 : ℕ) ^ 2 = 4 by norm_num,
      pow_four_eq_one, map_one, one_pow]
  have hw2 : w ^ 2 ^ (k + 2) = 1 := by
    have h1 : x ^ 2 ^ (k + 2) = 1 := by rw [pow_add, pow_mul, hk, one_pow]
    rwa [hxw, hcomm.mul_pow, hh, mul_one] at h1
  have hcop : Nat.Coprime (orderOf w) (2 ^ (k + 2)) :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hw3)
      (Nat.Coprime.pow_right _ (by norm_num))
  have hw1 : w = 1 :=
    orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one hw2))
  exact ⟨z, by rw [hxw, hw1, one_mul]⟩

end Finite

theorem fst_eq_zero_of_heisL_smul_mem_sublineOrbit [CharP K 2]
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (hC : C ≤ scalarCenter J)
    (z : hermitianUnipotentCoord J)
    (h : coverToPGL J C hJ hC (heisL J C hJ z) • unitaryCoordinatePoint (K := K) 2 ∈
      sublineOrbit J C hJ hC) : z.1.1 = 0 := by
  obtain ⟨_, ⟨m, rfl⟩, hm⟩ := h
  obtain ⟨hv, hmv⟩ := sublineHom_smul_point hJ m
  change ProjGenLinGroup.mk ((sublineHom J hJ m : J.specialSubgroup) : GL (Fin 3) K) •
    unitaryCoordinatePoint (K := K) 0 = _ at hm
  rw [hmv, coverToPGL_heisL, unitaryCoordinatePoint, Projectivization.PGL.mk_smul_mk,
    Projectivization.mk_eq_mk_iff] at hm
  obtain ⟨a, ha⟩ := hm
  have h1 : (a : K) * ((hermitianUnipotentMatrix J z) *ᵥ (Pi.single 2 1 : Fin 3 → K)) 1 = 0 :=
    congrFun ha 1
  rw [mulVec_single_one, hermitianUnipotentMatrix_eq] at h1
  simpa using h1

@[expose] def normScale (c : normOne J) (z : hermitianUnipotentCoord J) :
    hermitianUnipotentCoord J :=
  ⟨(((c : Kˣ) : K) * z.1.1, z.1.2), by
    have hc : ((c : Kˣ) : K) * J.conj ((c : Kˣ) : K) = 1 := c.2
    have hz := z.2
    dsimp only
    rw [map_mul]
    linear_combination hz + z.1.1 * J.conj z.1.1 * hc⟩

theorem normScale_mul_normScale (c d : normOne J) (z : hermitianUnipotentCoord J) :
    normScale c (normScale d z) = normScale (c * d) z :=
  Subtype.ext (Prod.ext (by simp [normScale, mul_assoc]) rfl)

theorem normScale_one (z : hermitianUnipotentCoord J) : normScale 1 z = z :=
  Subtype.ext (Prod.ext (by simp [normScale]) rfl)

@[expose] def normScaleCoord (c : normOne J) : MulAut (hermitianUnipotentCoord J) where
  toFun := normScale c
  invFun := normScale c⁻¹
  left_inv z := by rw [normScale_mul_normScale, inv_mul_cancel, normScale_one]
  right_inv z := by rw [normScale_mul_normScale, mul_inv_cancel, normScale_one]
  map_mul' z w := by
    have hc : ((c : Kˣ) : K) * J.conj ((c : Kˣ) : K) = 1 := c.2
    refine Subtype.ext (Prod.ext ?_ ?_)
    · change ((c : Kˣ) : K) * (z.1.1 + w.1.1) = ((c : Kˣ) : K) * z.1.1 + ((c : Kˣ) : K) * w.1.1
      ring
    · change z.1.2 + w.1.2 - z.1.1 * J.conj w.1.1 =
        z.1.2 + w.1.2 - ((c : Kˣ) : K) * z.1.1 * J.conj (((c : Kˣ) : K) * w.1.1)
      rw [map_mul]
      linear_combination z.1.1 * J.conj w.1.1 * hc

@[simp] theorem fst_normScaleCoord (c : normOne J) (z : hermitianUnipotentCoord J) :
    (normScaleCoord c z).1.1 = ((c : Kˣ) : K) * z.1.1 :=
  rfl

@[simp] theorem snd_normScaleCoord (c : normOne J) (z : hermitianUnipotentCoord J) :
    (normScaleCoord c z).1.2 = z.1.2 :=
  rfl

theorem sublineAutHom_inl_heisL [Finite K] (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hC : C ≤ scalarCenter J) (e : normOne J) (z : hermitianUnipotentCoord J) :
    sublineAutHom J C hJ hC (SemidirectProduct.inl e) (heisL J C hJ z) =
      heisL J C hJ (normScaleCoord e⁻¹ z) := by
  obtain ⟨hg, h⟩ := sublineAutHom_mk hJ hC (SemidirectProduct.inl e) (hermitianUnipotentSU J hJ z)
  change sublineAutHom J C hJ hC (SemidirectProduct.inl e)
    ((hermitianUnipotentSU J hJ z : J.specialSubgroup) : J.specialSubgroup ⧸ C) = _
  rw [h]
  change _ = ((hermitianUnipotentSU J hJ (normScaleCoord e⁻¹ z) : J.specialSubgroup) :
    J.specialSubgroup ⧸ C)
  congr 1
  have he : J.conj ((e : Kˣ) : K) = ((e : Kˣ) : K)⁻¹ := conj_eq_inv_of_mem_normOne J e.2
  have he0 : ((e : Kˣ) : K) ≠ 0 := (e : Kˣ).ne_zero
  apply Subtype.ext
  apply Units.ext
  simp only [SemidirectProduct.left_inl, SemidirectProduct.right_inl, OneMemClass.coe_one,
    map_one, MulAut.one_apply, Units.val_mul]
  rw [coe_diag3, coe_diag3_inv, coe_hermitianUnipotentSU, coe_hermitianUnipotentSU]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, normScaleCoord, normScale, map_mul, he]
  field_simp

theorem torus_mem_center_of_pow_three (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    {c : normOne J} (hc : ((c : Kˣ) : K) ^ 3 = 1) :
    QuotientGroup.mk' C (torusHom J hJ c) ∈ Subgroup.center (J.specialSubgroup ⧸ C) := by
  have hmem : torusHom J hJ c ∈ scalarCenter J := by
    refine mem_scalarCenter_of_scalar J hJ (c := ((c : Kˣ) : K)) ?_
    have key : (((c : Kˣ) : K) ^ 2)⁻¹ = ((c : Kˣ) : K) :=
      inv_eq_of_mul_eq_one_left (by rw [← pow_succ']; exact hc)
    rw [coe_torusHom, coe_diag3]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [scalar_apply, key]
  refine Subgroup.mem_center_iff.mpr fun x => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective C x
  rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (scalarCenter_le_center J hmem) x]

end CFSG.ShultStronglyClosedTI.UnitaryExcluded
