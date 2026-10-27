module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.Timmesfeld75.L2Defs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.L3

open Matrix CFSG.CGT.Timmesfeld75
open scoped MatrixGroups

variable {F : Type} [Field F] [Finite F] [CharP F 2]

@[expose] noncomputable def sqrtF (x : F) : F := x ^ (Nat.card F / 2)

theorem sqrtF_sq (x : F) : sqrtF x ^ 2 = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨k, hk, hcard⟩ := FiniteField.card F 2
  have hc : Nat.card F = 2 ^ (k : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  have h2 : Nat.card F / 2 * 2 = Nat.card F := by
    rw [hc]
    obtain ⟨m, hm⟩ : ∃ m, (k : ℕ) = m + 1 := ⟨(k : ℕ) - 1, by have := PNat.pos k; omega⟩
    rw [hm, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
  rw [sqrtF, ← pow_mul, h2, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card x

omit [Finite F] [CharP F 2] in
theorem sqrtF_mul (x y : F) : sqrtF (x * y) = sqrtF x * sqrtF y := by
  rw [sqrtF, sqrtF, sqrtF, mul_pow]

omit [Finite F] [CharP F 2] in
theorem sqrtF_one : sqrtF (1 : F) = 1 := by rw [sqrtF, one_pow]

omit [Finite F] [CharP F 2] in
@[expose] def stabM : Subgroup SL(3, F) where
  carrier := {g | g 2 0 = 0 ∧ g 2 1 = 0}
  one_mem' := ⟨by simp, by simp⟩
  mul_mem' := by
    rintro g h ⟨hg0, hg1⟩ ⟨hh0, hh1⟩
    refine ⟨?_, ?_⟩
    · show (g * h : Matrix (Fin 3) (Fin 3) F) 2 0 = 0
      rw [Matrix.mul_apply, Fin.sum_univ_three, hg0, hg1, hh0]
      ring
    · show (g * h : Matrix (Fin 3) (Fin 3) F) 2 1 = 0
      rw [Matrix.mul_apply, Fin.sum_univ_three, hg0, hg1, hh1]
      ring
  inv_mem' := by
    rintro g ⟨hg0, hg1⟩
    refine ⟨?_, ?_⟩
    · show (g⁻¹ : SL(3, F)) 2 0 = 0
      rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three]
      simp [hg0, hg1]
    · show (g⁻¹ : SL(3, F)) 2 1 = 0
      rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_three]
      simp [hg0, hg1]

@[expose] def blk (g : SL(3, F)) : Matrix (Fin 2) (Fin 2) F := !![g 0 0, g 0 1; g 1 0, g 1 1]

omit [Finite F] [CharP F 2] in
theorem blk_mul {g h : SL(3, F)} (hh : h ∈ stabM) : blk (g * h) = blk g * blk h := by
  obtain ⟨hh0, hh1⟩ := hh
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, hh0, hh1]

omit [Finite F] [CharP F 2] in
theorem det_blk_mul {g : SL(3, F)} (hg : g ∈ stabM) : (blk g).det * g 2 2 = 1 := by
  obtain ⟨hg0, hg1⟩ := hg
  have h := g.2
  rw [Matrix.det_fin_three, hg0, hg1] at h
  rw [blk, Matrix.det_fin_two_of]
  linear_combination h

omit [Finite F] [CharP F 2] in
theorem det_blk_ne_zero {g : SL(3, F)} (hg : g ∈ stabM) : (blk g).det ≠ 0 := by
  intro h
  have := det_blk_mul hg
  rw [h, zero_mul] at this
  exact zero_ne_one this

@[expose] noncomputable def rhoFun (g : SL(3, F)) (hg : g ∈ stabM) : SL(2, F) :=
  ⟨(sqrtF (blk g).det)⁻¹ • blk g, by
    rw [Matrix.det_smul, Fintype.card_fin, inv_pow, sqrtF_sq]
    exact inv_mul_cancel₀ (det_blk_ne_zero hg)⟩

theorem rhoFun_mul {g h : SL(3, F)} (hg : g ∈ stabM) (hh : h ∈ stabM) :
    rhoFun (g * h) (stabM.mul_mem hg hh) = rhoFun g hg * rhoFun h hh := by
  apply Subtype.ext
  show (sqrtF (blk (g * h)).det)⁻¹ • blk (g * h) =
    ((sqrtF (blk g).det)⁻¹ • blk g) * ((sqrtF (blk h).det)⁻¹ • blk h)
  rw [blk_mul hh, Matrix.det_mul, sqrtF_mul, mul_inv, smul_mul_smul_comm]

theorem rhoFun_one : rhoFun (1 : SL(3, F)) stabM.one_mem = 1 := by
  apply Subtype.ext
  have h1 : blk (1 : SL(3, F)) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [blk]
  simp only [rhoFun, h1, Matrix.det_one, sqrtF_one, inv_one, one_smul,
    Matrix.SpecialLinearGroup.coe_one]

@[expose] noncomputable def rho : ↥(stabM (F := F)) →* SL(2, F) where
  toFun g := rhoFun g g.2
  map_one' := rhoFun_one
  map_mul' g h := rhoFun_mul g.2 h.2

omit [Finite F] [CharP F 2] in
theorem transvection_01_mem (c : F) :
    SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c ∈ stabM (F := F) := by
  refine ⟨?_, ?_⟩ <;> simp [SpecialLinearGroup.transvection_coe]

omit [Finite F] [CharP F 2] in
theorem transvection_10_mem (c : F) :
    SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) c ∈ stabM (F := F) := by
  refine ⟨?_, ?_⟩ <;> simp [SpecialLinearGroup.transvection_coe]

theorem rho_transvection_01 (c : F) : rho ⟨_, transvection_01_mem c⟩ = utriElt c := by
  have hb : blk (SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) c) =
      !![1, c; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blk, SpecialLinearGroup.transvection_coe]
  apply Subtype.ext
  show (sqrtF (blk _).det)⁻¹ • blk _ = _
  rw [hb, Matrix.det_fin_two_of, mul_one, mul_zero, sub_zero, sqrtF_one, inv_one, one_smul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [utriElt_apply_00, utriElt_apply_01, utriElt_apply_10, utriElt_apply_11]

theorem rho_transvection_10 (c : F) : rho ⟨_, transvection_10_mem c⟩ = ltriElt c := by
  have hb : blk (SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) c) =
      !![1, 0; c, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blk, SpecialLinearGroup.transvection_coe]
  apply Subtype.ext
  show (sqrtF (blk _).det)⁻¹ • blk _ = _
  rw [hb, Matrix.det_fin_two_of, mul_one, zero_mul, sub_zero, sqrtF_one, inv_one, one_smul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ltriElt_apply_00, ltriElt_apply_01, ltriElt_apply_10, ltriElt_apply_11]

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.L3
