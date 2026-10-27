module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34E16

public section

namespace CFSG.Quasithin.H13.KGL34P

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Quasithin

variable {k : Type} [Field k]

@[expose] def cycSL : SpecialLinearGroup (Fin 3) k :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], by simp [Matrix.det_fin_three]⟩

theorem coe_cycSL :
    ((cycSL : SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
      !![0, 0, 1; 1, 0, 0; 0, 1, 0] := rfl

theorem cycSL_pow_three : (cycSL : SpecialLinearGroup (Fin 3) k) ^ 3 = 1 := by
  rw [pow_three]
  apply Subtype.ext
  change !![0, 0, 1; 1, 0, 0; 0, 1, 0] * (!![0, 0, 1; 1, 0, 0; 0, 1, 0] *
    !![0, 0, 1; 1, 0, 0; 0, 1, 0]) = (1 : Matrix (Fin 3) (Fin 3) k)
  simp only [mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

variable [CharP k 2] {ω : k}

theorem det_conjP1_mat (hω2 : ω ^ 2 + ω + 1 = 0) :
    Matrix.det (!![1, 1, 1; 1, ω ^ 2, ω; 1, ω, ω ^ 2] : Matrix (Fin 3) (Fin 3) k) = 1 := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  rw [Matrix.det_fin_three]
  simp
  first
    | ring1
    | linear_combination (ω^2 - ω - 3) * hω2 + (3*ω + 1) * h2

@[expose] def conjP1 (hω2 : ω ^ 2 + ω + 1 = 0) : SpecialLinearGroup (Fin 3) k :=
  ⟨!![1, 1, 1; 1, ω ^ 2, ω; 1, ω, ω ^ 2], det_conjP1_mat hω2⟩

theorem det_conjP2_mat (hω2 : ω ^ 2 + ω + 1 = 0) :
    Matrix.det (!![ω ^ 2, 1, 1; 1, 1, ω ^ 2; ω ^ 2, ω, ω ^ 2] : Matrix (Fin 3) (Fin 3) k) = 1 := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  rw [Matrix.det_fin_three]
  simp
  first
    | ring1
    | linear_combination (-ω^3 + 3*ω^2 - 2*ω - 3) * hω2 + (3*ω + 1) * h2

@[expose] def conjP2 (hω2 : ω ^ 2 + ω + 1 = 0) : SpecialLinearGroup (Fin 3) k :=
  ⟨!![ω ^ 2, 1, 1; 1, 1, ω ^ 2; ω ^ 2, ω, ω ^ 2], det_conjP2_mat hω2⟩

theorem det_conjP3_mat (hω2 : ω ^ 2 + ω + 1 = 0) :
    Matrix.det (!![ω, 1, 1; 1, ω, 1; ω, ω, ω ^ 2] : Matrix (Fin 3) (Fin 3) k) = 1 := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  rw [Matrix.det_fin_three]
  simp
  first
    | ring1
    | linear_combination (ω^2 - ω - 3) * hω2 + (3*ω + 1) * h2

@[expose] def conjP3 (hω2 : ω ^ 2 + ω + 1 = 0) : SpecialLinearGroup (Fin 3) k :=
  ⟨!![ω, 1, 1; 1, ω, 1; ω, ω, ω ^ 2], det_conjP3_mat hω2⟩

theorem cycSL_mul_conjP1 (hω3 : ω ^ 3 = 1) (hω2 : ω ^ 2 + ω + 1 = 0) :
    cycSL * conjP1 hω2 = conjP1 hω2 * torusDiag ω hω3 := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  apply Subtype.ext
  change !![0, 0, 1; 1, 0, 0; 0, 1, 0] * !![1, 1, 1; 1, ω ^ 2, ω; 1, ω, ω ^ 2] =
    !![1, 1, 1; 1, ω ^ 2, ω; 1, ω, ω ^ 2] * !![1, 0, 0; 0, ω, 0; 0, 0, ω ^ 2]
  simp only [mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> (try simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff]) <;> first
    | ring1
    | linear_combination (1 - ω) * hω2
    | linear_combination (-(1 - ω)) * hω2
    | linear_combination (-ω^2 + ω) * hω2

theorem torusDiag_cycSL_mul_conjP2 (hω3 : ω ^ 3 = 1) (hω2 : ω ^ 2 + ω + 1 = 0) :
    torusDiag ω hω3 * cycSL * conjP2 hω2 = conjP2 hω2 * torusDiag ω hω3 := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  apply Subtype.ext
  change !![1, 0, 0; 0, ω, 0; 0, 0, ω ^ 2] * !![0, 0, 1; 1, 0, 0; 0, 1, 0] *
    !![ω ^ 2, 1, 1; 1, 1, ω ^ 2; ω ^ 2, ω, ω ^ 2] =
    !![ω ^ 2, 1, 1; 1, 1, ω ^ 2; ω ^ 2, ω, ω ^ 2] * !![1, 0, 0; 0, ω, 0; 0, 0, ω ^ 2]
  simp only [mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> (try simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff]) <;> first
    | ring1
    | linear_combination (ω - 1) * hω2
    | linear_combination (-(ω - 1)) * hω2
    | linear_combination (-ω^2 + ω) * hω2

theorem torusDiag_sq_cycSL_mul_conjP3 (hω3 : ω ^ 3 = 1) (hω2 : ω ^ 2 + ω + 1 = 0) :
    torusDiag ω hω3 * torusDiag ω hω3 * cycSL * conjP3 hω2 =
      conjP3 hω2 * torusDiag ω hω3 := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  apply Subtype.ext
  change !![1, 0, 0; 0, ω, 0; 0, 0, ω ^ 2] * !![1, 0, 0; 0, ω, 0; 0, 0, ω ^ 2] *
    !![0, 0, 1; 1, 0, 0; 0, 1, 0] * !![ω, 1, 1; 1, ω, 1; ω, ω, ω ^ 2] =
    !![ω, 1, 1; 1, ω, 1; ω, ω, ω ^ 2] * !![1, 0, 0; 0, ω, 0; 0, 0, ω ^ 2]
  simp only [mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> (try simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff]) <;> first
    | ring1
    | linear_combination (ω - 1) * hω2
    | linear_combination (-(ω - 1)) * hω2
    | linear_combination (ω^2 - ω) * hω2
    | linear_combination (-(ω^2 - ω)) * hω2
    | linear_combination (ω^3 - ω^2) * hω2

omit [CharP k 2] in
theorem omega_ne_zero (hω3 : ω ^ 3 = 1) : ω ≠ 0 := by
  intro h
  rw [h] at hω3
  simp at hω3

@[expose] def scalarW2 (hω3 : ω ^ 3 = 1) : SpecialLinearGroup (Fin 3) k :=
  scalarElement (Units.mk0 (ω ^ 2) (pow_ne_zero 2 (omega_ne_zero hω3)))
    (by
      apply Units.ext
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
      rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hω3, one_pow])

omit [CharP k 2] in
theorem scalarW2_mem (hω3 : ω ^ 3 = 1) : scalarW2 hω3 ∈ scalars 3 k :=
  ⟨_, (by
      apply Units.ext
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
      rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hω3, one_pow]), rfl⟩

theorem cycSL_mul_torusDiag (hω3 : ω ^ 3 = 1) (hω2 : ω ^ 2 + ω + 1 = 0) :
    cycSL * torusDiag ω hω3 = scalarW2 hω3 * (torusDiag ω hω3 * cycSL) := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  apply Subtype.ext
  change !![0, 0, 1; 1, 0, 0; 0, 1, 0] * !![1, 0, 0; 0, ω, 0; 0, 0, ω ^ 2] =
    scalar (Fin 3) (ω ^ 2) * (!![1, 0, 0; 0, ω, 0; 0, 0, ω ^ 2] * !![0, 0, 1; 1, 0, 0; 0, 1, 0])
  rw [Matrix.scalar_apply]
  simp only [mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> (try simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff]) <;> first
    | ring1
    | linear_combination (1 - ω) * hω2
    | linear_combination (-(1 - ω)) * hω2
    | linear_combination (-ω^2 + ω) * hω2

theorem torusDiag_rad_conj (hω3 : ω ^ 3 = 1) (hω2 : ω ^ 2 + ω + 1 = 0) (b c : k) :
    torusDiag ω hω3 * rad b c * (torusDiag ω hω3)⁻¹ = rad (b * ω ^ 2) (c * ω) := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hω' : (ω ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hω3, one_pow]
  have ht : (torusDiag ω hω3)⁻¹ = torusDiag (ω ^ 2) hω' :=
    inv_eq_of_mul_eq_one_right (torusDiag_mul_sq ω hω3 hω')
  rw [ht]
  apply Subtype.ext
  change !![1, 0, 0; 0, ω, 0; 0, 0, ω ^ 2] * !![1, b, c; 0, 1, 0; 0, 0, 1] *
    !![1, 0, 0; 0, ω ^ 2, 0; 0, 0, (ω ^ 2) ^ 2] = !![1, b * ω ^ 2, c * ω; 0, 1, 0; 0, 0, 1]
  simp only [mul_fin_three]
  ext i j
  fin_cases i <;> fin_cases j <;> (try simp [-mul_eq_mul_left_iff, -mul_eq_mul_right_iff]) <;> first
    | ring1
    | linear_combination (c*ω^2 - c*ω) * hω2
    | linear_combination (-(c*ω^2 - c*ω)) * hω2
    | linear_combination (ω - 1) * hω2
    | linear_combination (-(ω - 1)) * hω2
    | linear_combination (ω^4 - ω^3 + ω - 1) * hω2

omit [CharP k 2] in
theorem proj_conj_of_mul_eq {A P D : SpecialLinearGroup (Fin 3) k} (h : A * P = P * D) :
    proj 3 k A = proj 3 k P * proj 3 k D * (proj 3 k P)⁻¹ := by
  rw [← map_inv, ← map_mul, ← map_mul, ← h]
  congr 1
  group

theorem proj_cycSL_commute (hω3 : ω ^ 3 = 1) (hω2 : ω ^ 2 + ω + 1 = 0) :
    proj 3 k cycSL * proj 3 k (torusDiag ω hω3) =
      proj 3 k (torusDiag ω hω3) * proj 3 k cycSL := by
  rw [← map_mul, ← map_mul, cycSL_mul_torusDiag hω3 hω2, map_mul,
    proj_eq_one_iff.mpr (scalarW2_mem hω3), one_mul]

theorem proj_cycSL_conj (hω3 : ω ^ 3 = 1) (hω2 : ω ^ 2 + ω + 1 = 0) :
    proj 3 k cycSL = proj 3 k (conjP1 hω2) * proj 3 k (torusDiag ω hω3) *
      (proj 3 k (conjP1 hω2))⁻¹ :=
  proj_conj_of_mul_eq (cycSL_mul_conjP1 hω3 hω2)

theorem proj_torusDiag_cycSL_conj (hω3 : ω ^ 3 = 1) (hω2 : ω ^ 2 + ω + 1 = 0) :
    proj 3 k (torusDiag ω hω3) * proj 3 k cycSL = proj 3 k (conjP2 hω2) *
      proj 3 k (torusDiag ω hω3) * (proj 3 k (conjP2 hω2))⁻¹ := by
  rw [← map_mul]
  exact proj_conj_of_mul_eq (torusDiag_cycSL_mul_conjP2 hω3 hω2)

theorem proj_torusDiag_sq_cycSL_conj (hω3 : ω ^ 3 = 1) (hω2 : ω ^ 2 + ω + 1 = 0) :
    proj 3 k (torusDiag ω hω3) ^ 2 * proj 3 k cycSL = proj 3 k (conjP3 hω2) *
      proj 3 k (torusDiag ω hω3) * (proj 3 k (conjP3 hω2))⁻¹ := by
  rw [pow_two, ← map_mul, ← map_mul]
  exact proj_conj_of_mul_eq (torusDiag_sq_cycSL_mul_conjP3 hω3 hω2)

theorem proj_torusDiag_rad_conj (hω3 : ω ^ 3 = 1) (hω2 : ω ^ 2 + ω + 1 = 0) (b c : k) :
    proj 3 k (torusDiag ω hω3) * proj 3 k (rad b c) * (proj 3 k (torusDiag ω hω3))⁻¹ =
      proj 3 k (rad (b * ω ^ 2) (c * ω)) := by
  rw [← map_inv, ← map_mul, ← map_mul, torusDiag_rad_conj hω3 hω2]

theorem norm_radP (hω3 : ω ^ 3 = 1) (hω2 : ω ^ 2 + ω + 1 = 0) {r : projectiveSL 3 k}
    (hr : r ∈ radP) :
    r * (proj 3 k (torusDiag ω hω3) * r * (proj 3 k (torusDiag ω hω3))⁻¹) *
      (proj 3 k (torusDiag ω hω3) ^ 2 * r * (proj 3 k (torusDiag ω hω3) ^ 2)⁻¹) = 1 := by
  obtain ⟨b, c, rfl⟩ := mem_radP.mp hr
  set y := proj 3 k (torusDiag ω hω3) with hy
  have e2 : y ^ 2 * proj 3 k (rad b c) * (y ^ 2)⁻¹ =
      proj 3 k (rad (b * ω ^ 2 * ω ^ 2) (c * ω * ω)) := by
    rw [show y ^ 2 * proj 3 k (rad b c) * (y ^ 2)⁻¹ =
      y * (y * proj 3 k (rad b c) * y⁻¹) * y⁻¹ by rw [pow_two]; group, hy,
      proj_torusDiag_rad_conj hω3 hω2, proj_torusDiag_rad_conj hω3 hω2]
  rw [e2, hy, proj_torusDiag_rad_conj hω3 hω2, ← map_mul, ← map_mul, rad_mul, rad_mul]
  have hb : b + b * ω ^ 2 + b * ω ^ 2 * ω ^ 2 = 0 := by
    linear_combination (b*ω^2 - b*ω + b) * hω2
  have hc : c + c * ω + c * ω * ω = 0 := by
    linear_combination c * hω2
  rw [hb, hc, rad_zero, map_one]

theorem exists_radP_eq (hω3 : ω ^ 3 = 1) (hω2 : ω ^ 2 + ω + 1 = 0) {r : projectiveSL 3 k}
    (hr : r ∈ radP) : ∃ s ∈ radP, r⁻¹ * (s * (proj 3 k (torusDiag ω hω3) * s *
      (proj 3 k (torusDiag ω hω3))⁻¹)⁻¹) = 1 := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  obtain ⟨b, c, rfl⟩ := mem_radP.mp hr
  refine ⟨proj 3 k (rad (b * ω ^ 2) (c * ω)), mem_radP.mpr ⟨_, _, rfl⟩, ?_⟩
  rw [proj_torusDiag_rad_conj hω3 hω2]
  have hinv : ∀ x z : k, (proj 3 k (rad x z))⁻¹ = proj 3 k (rad x z) := by
    intro x z
    rw [← map_inv]
    congr 1
    refine inv_eq_of_mul_eq_one_right ?_
    rw [rad_mul, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, rad_zero]
  simp only [hinv]
  rw [← map_mul, ← map_mul, rad_mul, rad_mul]
  have hb : b + (b * ω ^ 2 + b * ω ^ 2 * ω ^ 2) = 0 := by
    linear_combination (b*ω^2 - b*ω + b) * hω2
  have hc : c + (c * ω + c * ω * ω) = 0 := by
    linear_combination c * hω2
  rw [hb, hc, rad_zero, map_one]

theorem radP_le_closure (hk : Nat.card k = 4) (hω3 : ω ^ 3 = 1) (hω2 : ω ^ 2 + ω + 1 = 0) :
    radP ≤ Subgroup.closure {proj 3 k (rad 1 0), proj 3 k (rad ω 0), proj 3 k (rad 0 1),
      proj 3 k (rad 0 ω)} := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hω0 : ω ≠ 0 := omega_ne_zero hω3
  have hω1 : ω ≠ 1 := by
    intro h
    rw [h] at hω2
    have : (1 : k) = 0 := by linear_combination hω2 - h2
    exact one_ne_zero this
  set S := Subgroup.closure {proj 3 k (rad 1 0), proj 3 k (rad ω 0), proj 3 k (rad 0 1),
    proj 3 k (rad 0 ω)} with hS
  have m1 : proj 3 k (rad 1 0) ∈ S := Subgroup.subset_closure (by simp)
  have m2 : proj 3 k (rad ω 0) ∈ S := Subgroup.subset_closure (by simp)
  have m3 : proj 3 k (rad 0 1) ∈ S := Subgroup.subset_closure (by simp)
  have m4 : proj 3 k (rad 0 ω) ∈ S := Subgroup.subset_closure (by simp)
  have hb : ∀ b : k, proj 3 k (rad b 0) ∈ S := by
    intro b
    rcases LinearFieldFour.eq_zero_or_eq_one_or hk hω0 hω1 b with rfl | rfl | rfl | rfl
    · rw [rad_zero, map_one]
      exact S.one_mem
    · exact m1
    · exact m2
    · have e : rad (ω + 1) (0 : k) = rad ω 0 * rad 1 0 := by rw [rad_mul, add_zero]
      rw [e, map_mul]
      exact S.mul_mem m2 m1
  have hc : ∀ c : k, proj 3 k (rad 0 c) ∈ S := by
    intro c
    rcases LinearFieldFour.eq_zero_or_eq_one_or hk hω0 hω1 c with rfl | rfl | rfl | rfl
    · rw [rad_zero, map_one]
      exact S.one_mem
    · exact m3
    · exact m4
    · have e : rad (0 : k) (ω + 1) = rad 0 ω * rad 0 1 := by rw [rad_mul, add_zero]
      rw [e, map_mul]
      exact S.mul_mem m4 m3
  intro x hx
  obtain ⟨b, c, rfl⟩ := mem_radP.mp hx
  have e : rad b c = rad b 0 * rad 0 c := by rw [rad_mul, add_zero, zero_add]
  rw [e, map_mul]
  exact S.mul_mem (hb b) (hc c)

end CFSG.Quasithin.H13.KGL34P

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem exists_mulEquiv_radP {X : Type} [Group X] [Finite X] (hX : LieModel X .PSL 3 2 2)
    {R : Subgroup X} (hR : IsElemAbelian 2 R) (hcard : Nat.card R = 16) :
    ∃ (k : Type) (_ : Field k), Nat.card k = 4 ∧ ∃ e : X ≃* projectiveSL 3 k,
      R.map e.toMonoidHom = KGL34P.radP := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR2 : IsPGroup 2 R := IsPGroup.of_card (n := 4) (by rw [hcard]; norm_num)
  obtain ⟨S₀, hS₀, hRS₀⟩ := A4.exists_isSylowTwoOf_ge le_top hR2
  obtain ⟨k, _, hk, e, he⟩ := exists_mulEquiv_sylow_eq hX hS₀
  have : Finite k := LinearFieldFour.finite_of_card_eq_four hk
  have hEU : R.map e.toMonoidHom ≤ projUnitriangular 3 k := by
    rw [← he]
    exact Subgroup.map_mono hRS₀
  have hEab := isElemAbelian_map_mulEquiv e hR
  have hEcard : Nat.card (R.map e.toMonoidHom) = 16 := by
    rw [Subgroup.card_map_of_injective e.injective, hcard]
  rcases KGL34P.eq_radP_or_of_isElemAbelian hk hEU hEab hEcard with h1 | h1
  · exact ⟨k, inferInstance, hk, e, h1⟩
  · refine ⟨k, inferInstance, hk, e.trans (KGL34P.alpha0Aut hk)⁻¹, ?_⟩
    have h2 : R.map (e.trans (KGL34P.alpha0Aut hk)⁻¹).toMonoidHom =
        (R.map e.toMonoidHom).map ((KGL34P.alpha0Aut hk)⁻¹).toMonoidHom := by
      rw [Subgroup.map_map]
      rfl
    rw [h2, h1, KGL34P.map_map_mulAut, inv_mul_cancel]
    exact Subgroup.map_id _

end CFSG.Quasithin.H13
