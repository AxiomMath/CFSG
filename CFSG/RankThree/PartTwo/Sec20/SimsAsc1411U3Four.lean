module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411U3Torus

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {K : Type} [Field K]

theorem exists_pow_four_eq_add_one [Finite K] [CharP K 2] (hK : Nat.card K = 16) :
    ∃ z : K, z ^ 4 = z + 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hou : orderOf u = 15 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hu, Nat.card_units, hK]
  set x : K := (u : K) with hxdef
  have hx15 : x ^ 15 = 1 := by
    rw [hxdef, ← Units.val_pow_eq_pow_val, ← hou, pow_orderOf_eq_one, Units.val_one]
  have hne : ∀ k, 0 < k → k < 15 → x ^ k ≠ 1 := by
    intro k hk0 hk15 hk
    have : u ^ k = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hk)
    have := orderOf_le_of_pow_eq_one hk0 this
    omega
  have hx5 := hne 5 (by norm_num) (by norm_num)
  have hx3 := hne 3 (by norm_num) (by norm_num)
  have hx0 : x ≠ 0 := u.ne_zero
  have h10 : x ^ 10 + x ^ 5 + 1 = 0 := by
    have e : (x ^ 5 - 1) * (x ^ 10 + x ^ 5 + 1) = 0 := by linear_combination hx15
    rcases mul_eq_zero.1 e with e | e
    · exact absurd (sub_eq_zero.1 e) hx5
    · exact e
  have h3 : x ^ 2 + x + 1 ≠ 0 := by
    intro e
    apply hx3
    linear_combination (x - 1) * e
  have hphi : (x ^ 4 + x + 1) * (x ^ 4 + x ^ 3 + 1) = 0 := by
    have e : (x ^ 2 + x + 1) * ((x ^ 4 + x + 1) * (x ^ 4 + x ^ 3 + 1)) = 0 := by
      linear_combination h10 + (x ^ 9 + x ^ 8 + x ^ 7 + 2 * x ^ 6 + 2 * x ^ 5 + 2 * x ^ 4
        + x ^ 3 + x ^ 2 + x) * h2
    rcases mul_eq_zero.1 e with e | e
    · exact absurd e h3
    · exact e
  rcases mul_eq_zero.1 hphi with e | e
  · exact ⟨x, by linear_combination e - (x + 1) * h2⟩
  · refine ⟨x⁻¹, ?_⟩
    have hx4 : x ^ 4 ≠ 0 := pow_ne_zero 4 hx0
    field_simp
    linear_combination e - (x ^ 4 + x ^ 3) * h2

section Matrices

variable (z : K)

@[expose] def u34Mat : Matrix (Fin 3) (Fin 3) K :=
  !![0, z ^ 8, z ^ 7; z ^ 8, z ^ 11, 1; z ^ 7, 1, z ^ 4]

@[expose] def u34MatBar : Matrix (Fin 3) (Fin 3) K :=
  !![0, z ^ 2, z ^ 13; z ^ 2, z ^ 14, 1; z ^ 13, 1, z]

variable {z} (h2 : (2 : K) = 0) (hz : z ^ 4 = z + 1)

include h2 hz

theorem u34Mat_mul_bar : u34Mat z * u34MatBar z = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u34Mat, u34MatBar, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem u34MatBar_mul : u34MatBar z * u34Mat z = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u34Mat, u34MatBar, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem u34Mat_map_pow_four : (u34Mat z).map (· ^ 4) = u34MatBar z := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u34Mat, u34MatBar] <;> grind

theorem det_u34Mat : (u34Mat z).det = 1 := by
  rw [Matrix.det_fin_three]
  simp [u34Mat]
  grind

theorem u34Mat_pow_twelve : u34Mat z ^ 12 = u34MatBar z := by
  have e2 : u34Mat z ^ 2 =
      !![z ^ 7, z ^ 3, z ^ 7; z ^ 3, z ^ 3, z ^ 6; z ^ 7, z ^ 6, z ^ 13] := by
    rw [sq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [u34Mat, Matrix.mul_apply, Fin.sum_univ_three] <;> grind
  have e4 : u34Mat z ^ 4 =
      !![z ^ 6, z ^ 5, z ^ 8; z ^ 5, z ^ 12, z ^ 11; z ^ 8, z ^ 11, z ^ 3] := by
    rw [show 4 = 2 + 2 from rfl, pow_add, e2]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three] <;> grind
  have e8 : u34Mat z ^ 8 =
      !![z ^ 9, z ^ 14, z ^ 8; z ^ 14, z ^ 5, 1; z ^ 8, 1, z ^ 8] := by
    rw [show 8 = 4 + 4 from rfl, pow_add, e4]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three] <;> grind
  rw [show 12 = 8 + 4 from rfl, pow_add, e8, e4]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [u34MatBar, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

@[expose] def u34GL : GL (Fin 3) K :=
  ⟨u34Mat z, u34MatBar z, u34Mat_mul_bar h2 hz, u34MatBar_mul h2 hz⟩

theorem coe_u34GL : ((u34GL h2 hz : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = u34Mat z := rfl

theorem coe_u34GL_inv :
    (((u34GL h2 hz)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = u34MatBar z := rfl

theorem u34GL_pow_thirteen : u34GL h2 hz ^ 13 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, coe_u34GL, pow_succ, u34Mat_pow_twelve h2 hz,
    u34MatBar_mul h2 hz, Units.val_one]

theorem thirteen_dvd_of_pow_eq_scalar {j : ℕ} {c : Kˣ}
    (hj : u34GL h2 hz ^ j = GeneralLinearGroup.scalar (Fin 3) c) : 13 ∣ j := by
  by_contra hnd
  have hcop : Nat.Coprime j 13 := ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hnd).symm
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by norm_num)
  have h13 := u34GL_pow_thirteen h2 hz
  have hM : u34GL h2 hz = GeneralLinearGroup.scalar (Fin 3) (c ^ u) := by
    have e : u34GL h2 hz ^ (j * u) = u34GL h2 hz := by
      rw [← Nat.div_add_mod (j * u) 13, hu, pow_add, pow_mul, h13, one_pow, one_mul, pow_one]
    rw [← e, pow_mul, hj, map_pow]
  have h01 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 1) hM
  simp only [coe_u34GL, GeneralLinearGroup.coe_scalar, scalar_apply] at h01
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz
  simp [u34Mat, hz0] at h01

end Matrices

theorem thirteen_dvd_orderOf_fieldAut_mul_inv (h : UnitaryFieldData 2 2 K)
    (hC : IsPrimeFormGram (1 : GL (Fin 3) K)) (φ : K ≃+* K) (hφ : ∀ c, φ c = h.bar c) :
    ∃ x : primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
      13 ∣ orderOf (primeFormFieldAut h hC φ x * x⁻¹) := by
  have := h.finite
  have := h.charP
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  obtain ⟨z, hz⟩ := exists_pow_four_eq_add_one (K := K) (by rw [h.card]; norm_num)
  have hbar : ∀ c : K, h.bar c = c ^ 4 := fun c => by rw [UnitaryFieldData.bar_apply]; norm_num
  have hmapbar : (u34Mat z).map h.bar = u34MatBar z := by
    rw [← u34Mat_map_pow_four h2 hz]
    exact Matrix.ext fun i j => hbar _
  have hsymm : (u34MatBar z)ᵀ = u34MatBar z := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hmem : u34GL h2 hz ∈ gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [mem_gramSU_one_iff, coe_u34GL, hmapbar, hsymm]
    exact ⟨u34MatBar_mul h2 hz, det_u34Mat h2 hz⟩
  set y : gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := ⟨u34GL h2 hz, hmem⟩
  refine ⟨y, ?_⟩
  rw [fieldAut_mk_mul_inv]
  refine dvd_orderOf_mk_of_forall_scalar h _ fun k c hk => ?_
  have hφM : glAut φ (u34GL h2 hz) = (u34GL h2 hz)⁻¹ := by
    apply Units.ext
    rw [coe_glAut, coe_u34GL, coe_u34GL_inv, ← hmapbar]
    exact Matrix.ext fun i j => hφ _
  have hk' : (u34GL h2 hz) ^ (2 * k) = GeneralLinearGroup.scalar (Fin 3) c⁻¹ := by
    change ((glAut φ (u34GL h2 hz) * (u34GL h2 hz)⁻¹) ^ k : GL (Fin 3) K) = _ at hk
    rw [hφM, ← sq, ← pow_mul, inv_pow] at hk
    rw [map_inv, ← hk, inv_inv]
  have h13 := thirteen_dvd_of_pow_eq_scalar h2 hz hk'
  exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h13)

end CFSG.RankThree.PartTwo.Sec20
