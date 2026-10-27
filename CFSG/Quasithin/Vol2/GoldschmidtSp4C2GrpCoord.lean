module

public import CFSG.Quasithin.Vol2.Ch3E213MP6BM
public import CFSG.Quasithin.Vol2.Ch3E213MP6BE

public section

namespace CFSG.Quasithin.Ch3E213M.Sp4C2

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain (antiSp glMat uElt antiUnipotent
  mem_antiUnipotent_iff_upper uElt_mul uElt_inv minorAut)
open CFSG.Quasithin.SteinbergBS (upper_relations)
open CFSG.QuasithinUnique.Setup.X7b (uElt_inj)

variable {k : Type} [Field k] [CharP k 2]

theorem c2_coords [Finite k] {I : Subgroup (antiSp k)} (htr : ∀ x ∈ I, ¬ IsTransvection x)
    (htr' : ∀ x ∈ I, ¬ IsTransvection (minorAut k x)) {b c : k} (h : uElt 0 b c 0 ∈ I) :
    (b = 0 ∧ c = 0) ∨ (b ≠ 0 ∧ c ≠ 0) := by
  by_cases hb : b = 0
  · by_cases hc : c = 0
    · exact Or.inl ⟨hb, hc⟩
    · subst hb
      exact absurd (isTransvection_zl hc) (htr _ h)
  · by_cases hc : c = 0
    · subst hc
      refine absurd ?_ (htr' _ h)
      rw [P6B.minorAut_uElt_center]
      exact isTransvection_zl (pow_ne_zero 2 hb)
    · exact Or.inr ⟨hb, hc⟩

theorem c2_coord_inj_c [Finite k] {I : Subgroup (antiSp k)} (htr : ∀ x ∈ I, ¬ IsTransvection x)
    (htr' : ∀ x ∈ I, ¬ IsTransvection (minorAut k x)) {b b' c : k} (h : uElt 0 b c 0 ∈ I)
    (h' : uElt 0 b' c 0 ∈ I) : b = b' := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hm : uElt 0 (b + b') 0 0 ∈ I := by
    have e : uElt 0 b c 0 * (uElt 0 b' c 0)⁻¹ = uElt 0 (b + b') 0 0 := by
      rw [uElt_inv, uElt_mul]
      congr 1 <;> first | ring1 | linear_combination c * h2
    rw [← e]
    exact I.mul_mem h (I.inv_mem h')
  rcases c2_coords htr htr' hm with ⟨h1, -⟩ | ⟨-, h1⟩
  · linear_combination h1 - b' * h2
  · exact absurd rfl h1

theorem c2_coord_inj_b [Finite k] {I : Subgroup (antiSp k)} (htr : ∀ x ∈ I, ¬ IsTransvection x)
    (htr' : ∀ x ∈ I, ¬ IsTransvection (minorAut k x)) {b c c' : k} (h : uElt 0 b c 0 ∈ I)
    (h' : uElt 0 b c' 0 ∈ I) : c = c' := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hm : uElt 0 0 (c + c') 0 ∈ I := by
    have e : uElt 0 b c 0 * (uElt 0 b c' 0)⁻¹ = uElt 0 0 (c + c') 0 := by
      rw [uElt_inv, uElt_mul]
      congr 1 <;> first | ring1 | linear_combination b * h2
    rw [← e]
    exact I.mul_mem h (I.inv_mem h')
  rcases c2_coords htr htr' hm with ⟨-, h1⟩ | ⟨h1, -⟩
  · linear_combination h1 - c' * h2
  · exact absurd rfl h1

theorem eq_one_of_sq_eq_one' {x : k} (h : x ^ 2 = 1) : x = 1 := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have : (x - 1) ^ 2 = 0 := by linear_combination h + (1 - x) * h2
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)

theorem mem_unipotent_of_comm {b c : k} (hb : b ≠ 0) (hc : c ≠ 0) {x : antiSp k}
    (hx : x * uElt 0 b c 0 = uElt 0 b c 0 * x) : x ∈ antiUnipotent k := by
  have hconj : x * uElt 0 b c 0 * x⁻¹ = uElt 0 b c 0 := by
    calc x * uElt 0 b c 0 * x⁻¹ = uElt 0 b c 0 * x * x⁻¹ := by rw [hx]
      _ = uElt 0 b c 0 := by group
  have hup : IsUpper x := P6B.isUpper_of_conj_center hb hc hb hconj
  have hcj := P6B.conj_uElt_center hup b c
  rw [hconj] at hcj
  obtain ⟨-, e1, e2, -⟩ := uElt_inj hcj
  obtain ⟨r1, r2, -⟩ := upper_relations hup
  set M := glMat (x : GL (Fin 4) k) with hM
  have h00 : M 0 0 = 1 := by
    refine eq_one_of_sq_eq_one' ?_
    have : (M 0 0 ^ 2 - 1) * c = 0 := by linear_combination -e2
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hc)
  have h11 : M 1 1 = 1 := by
    have : (M 1 1 - 1) * b = 0 := by rw [h00] at e1; linear_combination -e1
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hb)
  have h33 : M 3 3 = 1 := by rw [h00, one_mul] at r1; exact r1
  have h22 : M 2 2 = 1 := by rw [h11, one_mul] at r2; exact r2
  refine (mem_antiUnipotent_iff_upper x).mpr ⟨hup, fun i => ?_⟩
  fin_cases i <;> assumption

end CFSG.Quasithin.Ch3E213M.Sp4C2
