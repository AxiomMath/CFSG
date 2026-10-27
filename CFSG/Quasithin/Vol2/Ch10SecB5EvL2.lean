module

public import CFSG.Quasithin.Vol2.Ch10SecB5EvProd
public import CFSG.Quasithin.Vol2.Ch10SecASL2OverQ
public import CFSG.Quasithin.Vol2.Ch10SecALiftSyl
public import CFSG.Quasithin.Vol2.Ch10SecATorus
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B4Dual
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.InternalSecB51
public import CFSG.Quasithin.Background.InternalSecFF
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime
public import CFSG.Quasithin.Vol2.Ch10SecA1012Three
public import CFSG.Quasithin.Vol2.Ch10SecA1012Two
public import CFSG.Quasithin.Vol2.Ch10SecB5Easy
public import CFSG.Quasithin.Vol2.Ch10SecB5EvLk
public import CFSG.Quasithin.Vol2.Ch10SecB5Gen
public import CFSG.Quasithin.Vol2.Ch10SecB5Obl
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.Vol2.Ch10.SecA (unipSL coe_unipSL unipSL_mul_self unipSL_zero)

section SL2

variable {F : Type} [Field F]

local notation "SL₂" => Matrix.SpecialLinearGroup (Fin 2) F

theorem upper_mul {h k : SL₂} (hh : (h : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (hk : (k : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    ((h * k : SL₂) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      ((h * k : SL₂) : Matrix (Fin 2) (Fin 2) F) 0 0 =
        (h : Matrix (Fin 2) (Fin 2) F) 0 0 * (k : Matrix (Fin 2) (Fin 2) F) 0 0 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hh, hk]

theorem upper_pow {h : SL₂} (hh : (h : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (n : ℕ) :
    ((h ^ n : SL₂) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      ((h ^ n : SL₂) : Matrix (Fin 2) (Fin 2) F) 0 0 = (h : Matrix (Fin 2) (Fin 2) F) 0 0 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    obtain ⟨h1, h2⟩ := upper_mul ih.1 hh
    exact ⟨h1, by rw [h2, ih.2, pow_succ]⟩

theorem upper_det {h : SL₂} (hh : (h : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    (h : Matrix (Fin 2) (Fin 2) F) 0 0 * (h : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
  have := h.2
  rw [Matrix.det_fin_two, hh, mul_zero, sub_zero] at this
  exact this

theorem eq_unipSL_of_upper {h : SL₂} (hh : (h : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (h00 : (h : Matrix (Fin 2) (Fin 2) F) 0 0 = 1) :
    h = unipSL ((h : Matrix (Fin 2) (Fin 2) F) 0 1) := by
  have hdet := upper_det hh
  rw [h00, one_mul] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_unipSL, hh, h00, hdet]

theorem upper_conj_unipSL {h : SL₂} (hh : (h : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (b : F) :
    h * unipSL b * h⁻¹ = unipSL ((h : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 * b) := by
  have hdet := upper_det hh
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_unipSL, Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two, hh]
  · linear_combination hdet
  · ring
  · linear_combination hdet

theorem exists_eq_mul_unipSL {g h : SL₂} (hg : (g : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (hh : (h : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (h00 : (g : Matrix (Fin 2) (Fin 2) F) 0 0 = (h : Matrix (Fin 2) (Fin 2) F) 0 0) :
    ∃ c : F, h = g * unipSL c := by
  have hdet := upper_det hg
  have h1 : ((g⁻¹ * h : SL₂) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, hg, hh]
  have h2 : ((g⁻¹ * h : SL₂) : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, hh, ← h00]
    linear_combination hdet
  refine ⟨((g⁻¹ * h : SL₂) : Matrix (Fin 2) (Fin 2) F) 0 1, ?_⟩
  rw [← eq_unipSL_of_upper h1 h2]
  group

variable [CharP F 2]

theorem sq_ne_one_of_orderOf_three {z : SL₂} (hz : (z : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (h3 : orderOf z = 3) : (z : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 ≠ 1 := by
  intro hsq
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have h1 : (z : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    have : ((z : Matrix (Fin 2) (Fin 2) F) 0 0 - 1) * ((z : Matrix (Fin 2) (Fin 2) F) 0 0 - 1) =
        0 := by
      linear_combination hsq + (1 - (z : Matrix (Fin 2) (Fin 2) F) 0 0) * h2
    exact sub_eq_zero.mp (mul_self_eq_zero.mp this)
  have hz2 : z ^ 2 = 1 := by
    rw [sq, eq_unipSL_of_upper hz h1, unipSL_mul_self]
  have := orderOf_dvd_of_pow_eq_one hz2
  rw [h3] at this
  norm_num at this

theorem eq_zero_of_upper_conj {z : SL₂} (hz : (z : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (h3 : orderOf z = 3) {b : F} (h : z * unipSL b * z⁻¹ = unipSL b) : b = 0 := by
  rw [upper_conj_unipSL hz] at h
  have hb := congrArg (fun A : SL₂ => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simp only [coe_unipSL] at hb
  simp at hb
  have hne := sq_ne_one_of_orderOf_three hz h3
  have : ((z : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 - 1) * b = 0 := by linear_combination hb
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd (sub_eq_zero.mp h1) hne
  · exact h1

theorem exists_pow_mul_unipSL {z h : SL₂} (hz : (z : Matrix (Fin 2) (Fin 2) F) 1 0 = 0)
    (h3 : orderOf z = 3) (hh : (h : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (hh3 : h ^ 3 = 1) :
    ∃ a : ℕ, ∃ c : F, h = z ^ a * unipSL c := by
  set μ := (z : Matrix (Fin 2) (Fin 2) F) 0 0 with hμ
  set ν := (h : Matrix (Fin 2) (Fin 2) F) 0 0 with hν
  have hμ3 : μ ^ 3 = 1 := by
    have hz3 : z ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one z
    have h1 := (upper_pow hz 3).2
    rw [hz3] at h1
    simpa using h1.symm
  have hν3 : ν ^ 3 = 1 := by
    have h1 := (upper_pow hh 3).2
    rw [hh3] at h1
    simpa using h1.symm
  have hμ1 : μ ≠ 1 := fun h1 => sq_ne_one_of_orderOf_three hz h3 (by rw [← hμ, h1, one_pow])
  have hs : 1 + μ + μ ^ 2 = 0 := by
    have : (μ - 1) * (1 + μ + μ ^ 2) = 0 := by linear_combination hμ3
    rcases mul_eq_zero.mp this with h1 | h1
    · exact absurd (sub_eq_zero.mp h1) hμ1
    · exact h1
  have hprod : (ν - 1) * (ν - μ) * (ν - μ ^ 2) = 0 := by
    linear_combination hν3 - hμ3 + (-ν ^ 2 + ν * μ) * hs
  have key : ∀ a : ℕ, μ ^ a = ν → ∃ c : F, h = z ^ a * unipSL c := fun a ha =>
    exists_eq_mul_unipSL (upper_pow hz a).1 hh (by rw [(upper_pow hz a).2, ha])
  rcases mul_eq_zero.mp hprod with h1 | h1
  · rcases mul_eq_zero.mp h1 with h2 | h2
    · exact ⟨0, key 0 (by rw [pow_zero, sub_eq_zero.mp h2])⟩
    · exact ⟨1, key 1 (by rw [pow_one, sub_eq_zero.mp h2])⟩
  · exact ⟨2, key 2 (sub_eq_zero.mp h1).symm⟩

end SL2

end CFSG.Quasithin.Vol2.Ch10.SecB
