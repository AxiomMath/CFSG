module

public import CFSG.LocalAnalysis.UniquenessCase.UCInspL2Quat
public import CFSG.LocalAnalysis.UniquenessCase.UCInspL2Abs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Insp

open Matrix CFSG.Open Subgroup
open scoped MatrixGroups

section Cube

variable {K : Type} [Field K]

theorem sl2_sq_of_cube (g : SL(2, K)) (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) :
    (g : Matrix (Fin 2) (Fin 2) K) * g + g + 1 = 0 := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) K).det = 1 := g.2
  have h3 : (g : Matrix (Fin 2) (Fin 2) K) * g * g = 1 := by
    have : (g : Matrix (Fin 2) (Fin 2) K) ^ 3 = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_pow, hg3]
      rfl
    simpa [pow_succ] using this
  obtain ⟨a, b, c, e, hM⟩ : ∃ a b c e : K, (g : Matrix (Fin 2) (Fin 2) K) = !![a, b; c, e] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  rw [hM, Matrix.det_fin_two_of] at hdet
  rw [hM] at h3 ⊢
  have h00 : (a * a + b * c) * a + (a * b + b * e) * c = 1 := by
    have := congrFun (congrFun h3 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    linear_combination this
  have h01 : (a * a + b * c) * b + (a * b + b * e) * e = 0 := by
    have := congrFun (congrFun h3 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    linear_combination this
  have h10 : (c * a + e * c) * a + (c * b + e * e) * c = 0 := by
    have := congrFun (congrFun h3 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    linear_combination this
  have h11 : (c * a + e * c) * b + (c * b + e * e) * e = 1 := by
    have := congrFun (congrFun h3 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    linear_combination this
  have hE00 : a * ((a + e) ^ 2 - 1) = a + e + 1 := by
    linear_combination (a * c * e + c * e) * h01 + (a ^ 2 * b) * h10 +
      (-a ^ 3 - a * b * c - b * c) * h11 +
      (-a * b * c * e + a ^ 2 * e ^ 2 - a * b * c - b * c * e + a * e + 2 * a + e + 1) * hdet
  have hE01 : b * ((a + e) ^ 2 - 1) = 0 := by
    linear_combination (a * e) * h01 + (-b ^ 2) * h10 +
      (-a ^ 2 * b - b ^ 2 * c - a * b * e - b * e ^ 2 + b) * hdet
  have hE10 : c * ((a + e) ^ 2 - 1) = 0 := by
    linear_combination (-b * c + a * e) * h10 +
      (-a ^ 2 * c - b * c ^ 2 - a * c * e - c * e ^ 2 + c) * hdet
  by_cases ht : a + e + 1 = 0
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination a * ht - hdet
    · linear_combination b * ht
    · linear_combination c * ht
    · linear_combination e * ht - hdet
  · exfalso
    have hq : (a + e) ^ 2 - 1 ≠ 0 := fun h0 => ht (by rw [h0, mul_zero] at hE00; exact hE00.symm)
    have hb : b = 0 := (mul_eq_zero.1 hE01).resolve_right hq
    have hc : c = 0 := (mul_eq_zero.1 hE10).resolve_right hq
    subst hb hc
    have hae : a * e = 1 := by linear_combination hdet
    have hprod : (a - 1) * (a + e + 1) = 0 := by
      linear_combination (1 - a ^ 2) * hae + e * h00
    have ha : a = 1 := by
      have := (mul_eq_zero.1 hprod).resolve_right ht
      linear_combination this
    have he : e = 1 := by
      rw [ha] at hae
      linear_combination hae
    apply hg1
    apply Subtype.ext
    rw [hM, ha, he]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

end Cube

section Lift

variable {K : Type} [Field K]

abbrev pslMk (K : Type) [Field K] : SL(2, K) →* PSL(2, K) :=
  QuotientGroup.mk' (Subgroup.center SL(2, K))

theorem sq_eq_one_of_mem_center {x : SL(2, K)} (hx : x ∈ Subgroup.center SL(2, K)) :
    x ^ 2 = 1 := by
  obtain ⟨r, hr, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hx
  rw [Fintype.card_fin] at hr
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hrx, ← map_pow, hr, map_one]
  rfl

theorem exists_lift {d : PSL(2, K)} (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) :
    ∃ g : SL(2, K), pslMk K g = d ∧
      (g : Matrix (Fin 2) (Fin 2) K) * g + g + 1 = 0 := by
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective d
  have hc3 : g₀ ^ 3 ∈ Subgroup.center SL(2, K) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hd3
  have hs2 : (g₀ ^ 3) ^ 2 = 1 := sq_eq_one_of_mem_center hc3
  have hg3 : (g₀ ^ 4) ^ 3 = 1 := by
    calc (g₀ ^ 4) ^ 3 = ((g₀ ^ 3) ^ 2) ^ 2 := by simp only [← pow_mul]
      _ = 1 := by rw [hs2, one_pow]
  have hπ : pslMk K (g₀ ^ 4) = QuotientGroup.mk g₀ := by
    rw [map_pow]
    show (QuotientGroup.mk g₀ : PSL(2, K)) ^ 4 = QuotientGroup.mk g₀
    rw [pow_succ, hd3, one_mul]
  have hg1 : g₀ ^ 4 ≠ 1 := fun h => hd1 (by rw [← hπ, h, map_one])
  exact ⟨g₀ ^ 4, hπ, sl2_sq_of_cube _ hg3 hg1⟩

end Lift

section Assembly

variable {K : Type} [Field K]

theorem psi_eq_one_iff (P : GL (Fin 2) K) (x : SL(2, K)) :
    pslMk K (conjSL P x) = 1 ↔ x ∈ Subgroup.center SL(2, K) :=
  (QuotientGroup.eq_one_iff _).trans (conjSL_mem_center_iff P x)

theorem psi_eq_iff (P : GL (Fin 2) K) (x y : SL(2, K)) :
    pslMk K (conjSL P x) = pslMk K (conjSL P y) ↔ x⁻¹ * y ∈ Subgroup.center SL(2, K) := by
  rw [← psi_eq_one_iff P, map_mul, map_mul, map_inv, map_inv, inv_mul_eq_one]

theorem psl_exists_klein [Finite K] (h2 : (2 : K) ≠ 0) (D : Subgroup PSL(2, K))
    (hD : Nat.card D = 3) :
    ∃ S : Subgroup PSL(2, K), IsElemAbelian 2 S ∧ Nat.card S = 4 ∧
      D ≤ normalizer (S : Set PSL(2, K)) ∧ ⁅D, S⁆ = S := by
  haveI : Fintype K := Fintype.ofFinite K
  have hodd : Fintype.card K % 2 = 1 := by
    refine FiniteField.odd_card_of_char_ne_two fun h => h2 ?_
    have h' : ((2 : ℕ) : K) = 0 := (ringChar.spec K 2).2 (by rw [h])
    simpa using h'
  obtain ⟨d, hDd, hd3, hd1⟩ := exists_gen_of_card_three D hD
  obtain ⟨g, hgπ, hg2⟩ := exists_lift hd3 hd1
  obtain ⟨a, b, hab⟩ := exists_two_squares (K := K) hodd
  obtain ⟨I, J, u, hI2, hJ2, hIJ, hI0, hJ0, hIJ0, huI, huJ, hu2, hu0⟩ := exists_quat h2 hab
  have hgns : ∀ c : K, (g : Matrix (Fin 2) (Fin 2) K) ≠ c • (1 : Matrix (Fin 2) (Fin 2) K) := by
    intro c hc
    have hdet : (c • (1 : Matrix (Fin 2) (Fin 2) K)).det = 1 := by rw [← hc]; exact g.2
    rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one] at hdet
    have hgc := mem_center_of_scalar c hdet hc
    apply hd1
    rw [← hgπ]
    exact (QuotientGroup.eq_one_iff g).2 hgc
  obtain ⟨Q, hQ⟩ := exists_conj (u : Matrix (Fin 2) (Fin 2) K) (g : Matrix (Fin 2) (Fin 2) K)
    hu2 hg2 hu0 hgns
  have hψu : pslMk K (conjSL Q u) = d := by rw [conjSL_eq_of_mul_eq Q hQ, hgπ]
  set ψ : SL(2, K) →* PSL(2, K) := (pslMk K).comp (conjSL Q) with hψ
  have hψ_apply : ∀ x, ψ x = pslMk K (conjSL Q x) := fun x => rfl
  have hx : ψ I * ψ I = 1 := by
    rw [← map_mul, hψ_apply]; exact (psi_eq_one_iff Q _).2 hI2
  have hy : ψ J * ψ J = 1 := by
    rw [← map_mul, hψ_apply]; exact (psi_eq_one_iff Q _).2 hJ2
  have hxy : ψ I * ψ J = ψ J * ψ I := by
    rw [← map_mul, ← map_mul, hψ_apply, hψ_apply, psi_eq_iff]
    simpa using hIJ
  have hx1 : ψ I ≠ 1 := fun h => hI0 ((psi_eq_one_iff Q I).1 h)
  have hy1 : ψ J ≠ 1 := fun h => hJ0 ((psi_eq_one_iff Q J).1 h)
  have hne : ψ I ≠ ψ J := fun h => hIJ0 ((psi_eq_iff Q I J).1 h)
  have hψu' : ψ u = d := hψu
  have hdx : d * ψ I * d⁻¹ = ψ I * ψ J := by
    calc d * ψ I * d⁻¹ = ψ (u * I * u⁻¹) := by rw [map_mul, map_mul, map_inv, hψu']
      _ = ψ (I * J) := by rw [huI]
      _ = ψ I * ψ J := map_mul ψ I J
  have hdy : d * ψ J * d⁻¹ = ψ I := by
    calc d * ψ J * d⁻¹ = ψ (u * J * u⁻¹) := by rw [map_mul, map_mul, map_inv, hψu']
      _ = ψ I := by rw [huJ]
  obtain ⟨S, hSa, hSc, hSn, hSk⟩ := exists_klein_of_triple hx hy hxy hx1 hy1 hne hdx hdy
  exact ⟨S, hSa, hSc, hDd ▸ hSn, hDd ▸ hSk⟩

end Assembly

end CFSG.LocalAnalysis.UniquenessCase.UCK.Insp
