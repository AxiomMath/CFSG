module

public import CFSG.CharacterTheory.PSL2Table.Basic
public import CFSG.Quasithin.Vol2.Ch10SecABasic
public import CFSG.Quasithin.Vol2.Ch10SecALift

public section

namespace CFSG.Quasithin.H13.L216

open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL coe_unipSL)
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem coe_inv_sl (g : SL(2, F)) :
    ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      !![(g : Matrix (Fin 2) (Fin 2) F) 1 1, -(g : Matrix (Fin 2) (Fin 2) F) 0 1;
        -(g : Matrix (Fin 2) (Fin 2) F) 1 0, (g : Matrix (Fin 2) (Fin 2) F) 0 0] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem det_sl (g : SL(2, F)) :
    (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) F) 0 1 * (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 := by
  have h := g.2
  rwa [Matrix.det_fin_two] at h

theorem coe_conj_unipSL (g : SL(2, F)) (b : F) :
    ((g * unipSL b * g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      !![1 - (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 0 * b,
        (g : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 * b;
        -((g : Matrix (Fin 2) (Fin 2) F) 1 0 ^ 2 * b),
        1 + (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (g : Matrix (Fin 2) (Fin 2) F) 1 0 * b] := by
  have hdet := det_sl g
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_inv_sl,
    coe_unipSL]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | linear_combination hdet | linear_combination (-1 : F) * hdet | ring

theorem lower_eq_zero_of_conj_unipSL {g : SL(2, F)} {b : F} (hb : b ≠ 0)
    (h : ((g * unipSL b * g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  rw [coe_conj_unipSL] at h
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, neg_eq_zero, mul_eq_zero] at h
  rcases h with h | h
  · exact pow_eq_zero_iff (by norm_num) |>.mp h
  · exact absurd h hb

theorem lower_eq_zero_of_normalizes (K : Subgroup SL(2, F))
    (hK : ∀ x ∈ K, ∃ b : F, x = unipSL b) {g : SL(2, F)}
    (hg : ∀ x ∈ K, g * x * g⁻¹ ∈ K) {b : F} (hb : b ≠ 0) (hbK : unipSL b ∈ K) :
    (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  obtain ⟨b', hb'⟩ := hK _ (hg _ hbK)
  apply lower_eq_zero_of_conj_unipSL hb
  rw [hb', coe_unipSL]
  simp

theorem conj_unipSL_of_upper {g : SL(2, F)} (hg : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (b : F) : g * unipSL b * g⁻¹ = unipSL ((g : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 * b) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [coe_conj_unipSL, coe_unipSL, hg]
  fin_cases i <;> fin_cases j <;> simp

theorem upper_mul_zero_zero {g h : SL(2, F)} (hg : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (hh : (h : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    ((g * h : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (h : Matrix (Fin 2) (Fin 2) F) 0 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hh]
  ring

theorem upper_mul_lower {g h : SL(2, F)} (hg : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (hh : (h : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    ((g * h : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hg, hh]
  ring

theorem upper_conj_zero_zero {g h : SL(2, F)} (hg : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (hh : (h : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    ((h * g * h⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 0 0 =
      (g : Matrix (Fin 2) (Fin 2) F) 0 0 := by
  have hdet := det_sl h
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_inv_sl]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.head_fin_const, hg, hh, neg_zero, zero_mul, mul_zero, add_zero,
    zero_add]
  linear_combination (g : Matrix (Fin 2) (Fin 2) F) 0 0 * hdet +
    (g : Matrix (Fin 2) (Fin 2) F) 0 0 * (h : Matrix (Fin 2) (Fin 2) F) 0 1 * hh

theorem mem_U0_iff (x : SL(2, F)) : x ∈ CFSG.PSL2Table.unipSL F ↔ ∃ b : F, x = unipSL b := by
  constructor
  · intro hx
    rw [CFSG.PSL2Table.mem_unipSL_iff] at hx
    refine ⟨(x : Matrix (Fin 2) (Fin 2) F) 0 1, ?_⟩
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [coe_unipSL]
    fin_cases i <;> fin_cases j <;> simp [hx.1, hx.2.1, hx.2.2]
  · rintro ⟨b, rfl⟩
    rw [CFSG.PSL2Table.mem_unipSL_iff, coe_unipSL]
    simp

theorem borel_le_normalizer_unipSL (g : SL(2, F)) (hg : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (x : SL(2, F)) (hx : x ∈ CFSG.PSL2Table.unipSL F) :
    g * x * g⁻¹ ∈ CFSG.PSL2Table.unipSL F := by
  obtain ⟨b, rfl⟩ := (mem_U0_iff x).mp hx
  rw [conj_unipSL_of_upper hg]
  exact (mem_U0_iff _).mpr ⟨_, rfl⟩

end CFSG.Quasithin.H13.L216
