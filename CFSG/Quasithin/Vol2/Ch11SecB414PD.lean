module

public import CFSG.Quasithin.Vol2.Ch11SecB414PB
public import CFSG.Quasithin.Vol2.Ch11SecB414MJ
public import CFSG.Quasithin.Vol2.Ch11SecB414MC
public import CFSG.Quasithin.Vol2.Ch11SecS12O
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Quasithin.H13.Ch4.B414.M

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Matrix
open CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS (S12.entries_of_normalizer_zero S12.block_of_mem_sc_zero)

variable {F : Type} [Field F]

theorem conj_uMat_normal [CharP F 2] {a b c d : F} (had : a ≠ d) :
    (uMat ![b / (a + d), c / (a + d)] : Matrix (Fin 3) (Fin 3) F) * !![a, b, c; 0, d, 0; 0, 0, d] *
        ((uMat ![b / (a + d), c / (a + d)])⁻¹ : SpecialLinearGroup (Fin 3) F) =
      Matrix.diagonal ![a, d, d] := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hs : a + d ≠ 0 := fun h => had (by linear_combination h - d * h2)
  rw [Matrix.SpecialLinearGroup.coe_inv, coe_uMat]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.adjugate_fin_three]
  · field_simp
    linear_combination b * d * h2
  · field_simp
    linear_combination c * d * h2

omit [Field F] in
theorem eq_one_of_sq_cube {H : Type} [Group H] {y : H} (h2 : y ^ 2 = 1) (h3 : y ^ 3 = 1) :
    y = 1 := by
  have e : y = y ^ 3 * (y ^ 2)⁻¹ := by group
  rw [e, h2, h3, inv_one, mul_one]

theorem map_conj_of_mem {H : Type} [Group H] {K : Subgroup H} {c : H} (hc : c ∈ K) :
    K.map (MulAut.conj c).toMonoidHom = K := by
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact K.mul_mem (K.mul_mem hc hp) (K.inv_mem hc)
  · intro hx
    refine ⟨c⁻¹ * x * c, K.mul_mem (K.mul_mem (K.inv_mem hc) hx) hc, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem mk_uMat_mem_Ptheta (v : Fin 2 → F) :
    ProjGenLinGroup.mk (SpecialLinearGroup.toGL (uMat v)) ∈ Ptheta F 0 := by
  have hu : uMat v ∈ stabilizer (flagSpace 3 F (((0 : Fin 2) : ℕ) + 1)) :=
    mem_stabilizer_one_iff.mpr ⟨by simp [coe_uMat], by simp [coe_uMat]⟩
  exact ⟨proj 3 F (uMat v), ⟨uMat v, hu, rfl⟩, thetaP_proj (uMat v)⟩

variable [Finite F] [CharP F 2]

theorem exists_conj_normal (hF : Nat.card F = 4) {Y : Subgroup (PGL3 F)} (hY3 : Nat.card Y = 3)
    (hYL : ∀ y ∈ Y, ∀ p ∈ Ptheta F 0, y * p * y⁻¹ * p⁻¹ ∈ pCoreOf 2 (Ptheta F 0)) :
    ∃ g : GL (Fin 3) F, ∃ ν : Fˣ, ν ≠ 1 ∧
      (Ptheta F 0).map (MulAut.conj (ProjGenLinGroup.mk g)).toMonoidHom = Ptheta F 0 ∧
      Y.map (MulAut.conj (ProjGenLinGroup.mk g)).toMonoidHom =
        Subgroup.zpowers (ProjGenLinGroup.mk (dgHom ν)) := by
  have h2F : (2 : F) = 0 := CharTwo.two_eq_zero
  have : Finite ↥Y := Nat.finite_of_card_ne_zero (by rw [hY3]; norm_num)
  have : Nontrivial ↥Y := Finite.one_lt_card_iff_nontrivial.mp (by rw [hY3]; norm_num)
  obtain ⟨⟨y, hyY⟩, hy1⟩ := exists_ne (1 : ↥Y)
  have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hy3 : y ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ↥Y) (x := ⟨y, hyY⟩)
    rw [hY3] at h
    exact congrArg Subtype.val h
  have hY : Y = Subgroup.zpowers y := by
    have hle : Subgroup.zpowers y ≤ Y := Subgroup.zpowers_le.mpr hyY
    have hord : orderOf y = 3 := orderOf_eq_prime hy3 hy1'
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [hY3, Nat.card_zpowers, hord]
  have hPN : ∀ z ∈ Y, ∀ p ∈ Ptheta F 0, z * p * z⁻¹ ∈ Ptheta F 0 := fun z hz p hp => by
    have h1 := CFSG.LieType.BorelTits.pCoreOf_le 2 _ (hYL z hz p hp)
    have e : z * p * z⁻¹ = (z * p * z⁻¹ * p⁻¹) * p := by group
    rw [e]
    exact Subgroup.mul_mem _ h1 hp
  have hyN : y ∈ Subgroup.normalizer (Ptheta F 0 : Set (PGL3 F)) :=
    Subgroup.mem_normalizer_iff.mpr fun p => ⟨hPN y hyY p, fun h => by
      have h1 := hPN y⁻¹ (Subgroup.inv_mem _ hyY) _ h
      simpa [mul_assoc] using h1⟩
  have hysc : y ∈ sectionCentralizer (Ptheta F 0) (pCoreOf 2 (Ptheta F 0)) :=
    ⟨hyN, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hyN, hYL y hyY⟩
  obtain ⟨h, rfl⟩ := ProjGenLinGroup.mk_surjective y
  obtain ⟨h10, h20⟩ := S12.entries_of_normalizer_zero hF hysc.2.1
  obtain ⟨h12, h21, h1122⟩ := S12.block_of_mem_sc_zero hF hysc h10 h20
  set a := (h : Matrix (Fin 3) (Fin 3) F) 0 0 with ha
  set b := (h : Matrix (Fin 3) (Fin 3) F) 0 1 with hb
  set c := (h : Matrix (Fin 3) (Fin 3) F) 0 2 with hc
  set d := (h : Matrix (Fin 3) (Fin 3) F) 1 1 with hd
  have hform : (h : Matrix (Fin 3) (Fin 3) F) = !![a, b, c; 0, d, 0; 0, 0, d] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h10, h20, h12, h21, ← h1122, ha, hb, hc, hd]
  have hdet0 : (h : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]
    exact (Matrix.GeneralLinearGroup.det h).ne_zero
  have hdet : (h : Matrix (Fin 3) (Fin 3) F).det = a * d * d := by
    rw [hform, Matrix.det_fin_three]
    simp
  rw [hdet] at hdet0
  have ha0 : a ≠ 0 := fun h0 => hdet0 (by rw [h0]; ring)
  have hd0 : d ≠ 0 := fun h0 => hdet0 (by rw [h0]; ring)
  have had : a ≠ d := by
    intro had
    apply hy1'
    have h3 : ProjGenLinGroup.mk h =
        ProjGenLinGroup.mk (SpecialLinearGroup.toGL (uMat ![b / d, c / d])) := by
      rw [ProjGenLinGroup.mk_eq_mk_iff]
      refine ⟨(Units.mk0 d hd0)⁻¹, Units.ext ?_⟩
      rw [Units.val_mul, GeneralLinearGroup.coe_scalar, SpecialLinearGroup.coe_GL_coe_matrix,
        coe_uMat, hform, had]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, hd0] <;>
        field_simp
    have hsq : ProjGenLinGroup.mk h ^ 2 = 1 := by
      rw [h3, ← map_pow, ← map_pow, sq, ← uMat_add]
      have e : (![b / d, c / d] + ![b / d, c / d] : Fin 2 → F) = 0 := by
        funext i
        fin_cases i <;> simp [← two_mul, h2F]
      rw [e, uMat_zero, map_one, map_one]
    exact eq_one_of_sq_cube hsq hy3
  set u := uMat ![b / (a + d), c / (a + d)] with hu
  set ν : Fˣ := Units.mk0 (a / d) (div_ne_zero ha0 hd0) with hν
  refine ⟨SpecialLinearGroup.toGL u, ν, fun h1 => had ?_, map_conj_of_mem (mk_uMat_mem_Ptheta _),
    ?_⟩
  · have h2 := congrArg Units.val h1
    rw [hν, Units.val_mk0, Units.val_one, div_eq_one_iff_eq hd0] at h2
    exact h2
  · rw [hY, MonoidHom.map_zpowers]
    congr 1
    show ProjGenLinGroup.mk (SpecialLinearGroup.toGL u) * ProjGenLinGroup.mk h *
      (ProjGenLinGroup.mk (SpecialLinearGroup.toGL u))⁻¹ = ProjGenLinGroup.mk (dgHom ν)
    rw [← map_inv, ← map_mul, ← map_mul, ProjGenLinGroup.mk_eq_mk_iff]
    refine ⟨(Units.mk0 d hd0)⁻¹, Units.ext ?_⟩
    have hc' := conj_uMat_normal (b := b) (c := c) had
    rw [Units.val_mul, Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar, coe_dgHom,
      ← map_inv, SpecialLinearGroup.coe_GL_coe_matrix, SpecialLinearGroup.coe_GL_coe_matrix,
      hform, hc']
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hν, hd0]
    field_simp

end CFSG.Quasithin.H13.Ch4.B414.M
