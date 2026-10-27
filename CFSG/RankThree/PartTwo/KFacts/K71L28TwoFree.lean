module

public import CFSG.RankThree.PartTwo.Sec8.Notation
public import CFSG.Walter.PSL2Facts.Even

public noncomputable section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open Matrix
open scoped MatrixGroups

section Mat2

variable {K : Type*} [Field K] [CharP K 2]

theorem mat2_sq_eq_trace_smul_add_one {M : Matrix (Fin 2) (Fin 2) K} (hM : M.det = 1) :
    M ^ 2 = M.trace • M + 1 := by
  rw [Matrix.det_fin_two] at hM
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sq, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two] <;>
    first
      | ring1
      | linear_combination (-1 : K) * hM - h2

theorem mat2_pow_six_eq_one_of_trace {M : Matrix (Fin 2) (Fin 2) K} (hM : M.det = 1)
    (ht : M.trace = 0 ∨ M.trace = 1) : M ^ 6 = 1 := by
  have hsq := mat2_sq_eq_trace_smul_add_one hM
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rcases ht with ht | ht
  · rw [ht, zero_smul, zero_add] at hsq
    rw [show 6 = 2 * 3 by norm_num, pow_mul, hsq, one_pow]
  · rw [ht, one_smul] at hsq
    have h3 : M ^ 3 = 1 := by
      rw [pow_succ, hsq, add_mul, one_mul, ← sq, hsq, add_comm M 1, add_assoc, ← two_smul K M, h2,
        zero_smul, add_zero]
    rw [show 6 = 3 * 2 by norm_num, pow_mul, h3, one_pow]

theorem mat2_trace_eq_one_of_pow_three {U : Matrix (Fin 2) (Fin 2) K} (hU : U.det = 1)
    (hU3 : U ^ 3 = 1) (hU1 : U ≠ 1) : U.trace = 1 := by
  set t := U.trace with ht
  have hsq : U ^ 2 = t • U + 1 := mat2_sq_eq_trace_smul_add_one hU
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hcube : U ^ 3 = (t ^ 2 + 1) • U + t • 1 := by
    rw [pow_succ', hsq, mul_add, mul_smul_comm, ← sq, hsq, smul_add, smul_smul, mul_one, add_smul,
      one_smul, ← sq]
    abel
  rw [hU3] at hcube
  by_contra hne
  have hne' : t + 1 ≠ 0 := fun h => hne (by linear_combination h - h2)
  have hsq1 : t ^ 2 + 1 = (t + 1) ^ 2 := by linear_combination (-t) * h2
  have hUs : U = (t + 1)⁻¹ • 1 := by
    have h1 : (t ^ 2 + 1) • U = (t + 1) • 1 := by
      rw [eq_sub_of_add_eq hcube.symm, add_smul, one_smul, sub_eq_add_neg, ← neg_smul,
        CharTwo.neg_eq, add_comm]
    rw [hsq1, sq, ← smul_smul] at h1
    have h6 : (t + 1) • U = (1 : Matrix (Fin 2) (Fin 2) K) := by
      have h7 := congrArg (fun M => (t + 1)⁻¹ • M) h1
      simp only [smul_smul, ← mul_assoc, inv_mul_cancel₀ hne', one_mul, one_smul] at h7
      exact h7
    calc U = (t + 1)⁻¹ • ((t + 1) • U) := by rw [smul_smul, inv_mul_cancel₀ hne', one_smul]
      _ = (t + 1)⁻¹ • 1 := by rw [h6]
  have hdet := hU
  rw [hUs, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
  have hc : (t + 1)⁻¹ = 1 := CharTwo.sq_injective (show (t + 1)⁻¹ ^ 2 = 1 ^ 2 by
    rw [hdet, one_pow])
  exact hU1 (by rw [hUs, hc, one_smul])

omit [CharP K 2] in
theorem det_smul_one_add_smul (U : Matrix (Fin 2) (Fin 2) K) (a b : K) :
    (a • (1 : Matrix (Fin 2) (Fin 2) K) + b • U).det =
      a ^ 2 + a * b * U.trace + b ^ 2 * U.det := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two, Matrix.trace_fin_two]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
  ring1

theorem mat2_pow_nine_eq_one_of_commute (hK : Nat.card K = 8) {U Y : Matrix (Fin 2) (Fin 2) K}
    (hU : U.det = 1) (hU3 : U ^ 3 = 1) (hU1 : U ≠ 1) (hY : Y.det = 1) (hYU : Y * U = U * Y) :
    Y ^ 9 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have := Fintype.ofFinite K
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have ht := mat2_trace_eq_one_of_pow_three hU hU3 hU1
  have hsq : U ^ 2 = U + 1 := by rw [mat2_sq_eq_trace_smul_add_one hU, ht, one_smul]
  have hc : Fintype.card K = 8 := by rw [← Nat.card_eq_fintype_card, hK]
  have hfrob : ∀ x : K, x ^ 8 = x := fun x => by rw [← hc]; exact FiniteField.pow_card x
  have hq : U 0 1 ≠ 0 := by
    intro h0
    have h00 : U 0 0 ^ 2 = U 0 0 + 1 := by
      have h1 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) hsq
      simp only [sq, Matrix.mul_apply, Fin.sum_univ_two, h0, zero_mul, add_zero,
        Matrix.add_apply, Matrix.one_apply_eq] at h1
      rw [sq]
      exact h1
    have hp3 : U 0 0 ^ 3 = 1 := by linear_combination (U 0 0 + 1) * h00 + U 0 0 * h2
    have hp7 : U 0 0 ^ 7 = 1 := by
      have hp0 : U 0 0 ≠ 0 := fun hp => by
        rw [hp] at h00
        simp at h00
      have h1 := FiniteField.pow_card_sub_one_eq_one (U 0 0) hp0
      rwa [hc] at h1
    have hp1 : U 0 0 = 1 := by
      have h4 : U 0 0 ^ 7 = U 0 0 := by
        rw [show 7 = 3 * 2 + 1 by norm_num, pow_add, pow_mul, hp3, one_pow, one_mul, pow_one]
      exact h4.symm.trans hp7
    rw [hp1] at h00
    have : (1 : K) = 0 := by linear_combination h00 + h2
    exact one_ne_zero this
  obtain ⟨b, hb⟩ : ∃ b, b = Y 0 1 / U 0 1 := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, a = Y 0 0 - b * U 0 0 := ⟨_, rfl⟩
  have e00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 0) hYU
  have e01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M 0 1) hYU
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01
  have hYab : Y = a • (1 : Matrix (Fin 2) (Fin 2) K) + b • U := by
    have hbq : b * U 0 1 = Y 0 1 := by rw [hb, div_mul_cancel₀ _ hq]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ha]
    · rw [hbq]
    ·
      apply mul_left_cancel₀ hq
      linear_combination (-1 : K) * e00 - U 1 0 * hbq
    ·
      apply mul_left_cancel₀ hq
      linear_combination (-1 : K) * e01 - (U 1 1 - U 0 0) * hbq
  have hcomm : Commute (a • (1 : Matrix (Fin 2) (Fin 2) K)) (b • U) :=
    ((Commute.one_left U).smul_left a).smul_right b
  have hU8 : U ^ 8 = U + 1 := by
    rw [show 8 = 3 * 2 + 2 by norm_num, pow_add, pow_mul, hU3, one_pow, one_mul, hsq]
  have h8 : (a • (1 : Matrix (Fin 2) (Fin 2) K) + b • U) ^ 8 = (a + b) • 1 + b • U := by
    have h1 := add_pow_char_pow_of_commute 2 3 hcomm
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num] at h1
    rw [h1, smul_pow, smul_pow, one_pow, hU8, hfrob, hfrob, smul_add, add_smul]
    abel
  have hdetY := hY
  rw [hYab, det_smul_one_add_smul, ht, hU, mul_one, mul_one] at hdetY
  rw [hYab, show 9 = 8 + 1 by norm_num, pow_succ, h8]
  rw [add_mul, mul_add, mul_add, smul_mul_smul, smul_mul_smul, smul_mul_smul, smul_mul_smul,
    Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, ← sq U, hsq]
  have h3 : ((a + b) * a) • (1 : Matrix (Fin 2) (Fin 2) K) + ((a + b) * b) • U +
      ((b * a) • U + (b * b) • (U + 1)) =
        (a ^ 2 + a * b + b ^ 2) • 1 + ((2 : K) * (a * b + b * b)) • U := by
    rw [smul_add]
    module
  rw [h3, hdetY, h2, zero_mul, zero_smul, add_zero, one_smul]

end Mat2

theorem psl28_eq_bot_of_normalizes {x : PSL(2, GaloisField 2 3)} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    {X : Subgroup PSL(2, GaloisField 2 3)} (h2 : IsPGroup 2 X)
    (hXx : ∀ y ∈ X, x * y * x⁻¹ ∈ X) : X = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hX
  obtain ⟨t, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hX
  obtain ⟨U, hXU⟩ := h2.exists_le_sylow
  have hf : 2 ≤ 3 := by norm_num
  have htU : (t : PSL(2, GaloisField 2 3)) ∈ (U : Subgroup PSL(2, GaloisField 2 3)) := hXU t.2
  have ht1' : (t : PSL(2, GaloisField 2 3)) ≠ 1 := fun h => ht1 (Subtype.ext h)
  have hCt := CFSG.Walter.psl2_even_centralizer_involution hf U htU ht1'
  have hxt : x * t * x⁻¹ ∈ (U : Subgroup PSL(2, GaloisField 2 3)) := hXU (hXx t t.2)
  have hxt1 : x * t * x⁻¹ ≠ 1 := fun h => ht1' (by
    have h' : t = x⁻¹ * (x * t * x⁻¹) * x := by group
    rw [h', h, mul_one, inv_mul_cancel])
  have hCxt := CFSG.Walter.psl2_even_centralizer_involution hf U hxt hxt1
  have hxU : ∀ g ∈ (U : Subgroup PSL(2, GaloisField 2 3)),
      x * g * x⁻¹ ∈ (U : Subgroup PSL(2, GaloisField 2 3)) := by
    intro g hg
    rw [← hCt, Subgroup.mem_centralizer_singleton_iff] at hg
    rw [← hCxt, Subgroup.mem_centralizer_singleton_iff]
    calc x * g * x⁻¹ * (x * t * x⁻¹) = x * (g * t) * x⁻¹ := by group
      _ = x * (t * g) * x⁻¹ := by rw [hg]
      _ = x * t * x⁻¹ * (x * g * x⁻¹) := by group
  have hxN : x ∈ Subgroup.normalizer ((U : Subgroup PSL(2, GaloisField 2 3)) :
      Set PSL(2, GaloisField 2 3)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨hxU g, fun hg => ?_⟩
    have h1 := hxU _ (hxU _ hg)
    have hx3' : x * x * x = 1 := by
      rw [pow_succ, pow_two] at hx3
      exact hx3
    have h3 : x * (x * (x * g * x⁻¹) * x⁻¹) * x⁻¹ = g := by
      rw [show x * (x * (x * g * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * g * (x * x * x)⁻¹ by group,
        hx3', one_mul, inv_one, mul_one]
    rwa [h3] at h1
  have hcard := CFSG.Walter.psl2_even_card_normalizer_sylow_two (f := 3) (by norm_num) U
  have hox : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hdvd := orderOf_dvd_natCard (⟨x, hxN⟩ : Subgroup.normalizer
    ((U : Subgroup PSL(2, GaloisField 2 3)) : Set PSL(2, GaloisField 2 3)))
  rw [Subgroup.orderOf_mk, hox, hcard] at hdvd
  norm_num at hdvd

theorem not_invTwoBarNontrivial_of_inducedAutHom_eq_conj_psl28 {G : Type} [Group G] [Finite G]
    {L A : Subgroup G} (e : L ⧸ aschbacherSolvableCore 3 L ≃* PSL(2, GaloisField 2 3)) {b : G}
    (hbA : b ∈ A) (hb : b ∈ Subgroup.normalizer (L : Set G)) {w : PSL(2, GaloisField 2 3)}
    (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1) (hbw : inducedAutHom L e ⟨b, hb⟩ = MulAut.conj w) :
    ¬ Sec8.InvTwoBarNontrivial A L := by
  rintro ⟨X, hX1, hX2, hXinv⟩
  have hτ : thetaQuotMulAut L (L.normalizerMonoidHom ⟨b, hb⟩) ∈ autThetaQuot A L :=
    mem_autThetaQuot_iff.2 ⟨b, hb, hbA, rfl⟩
  set Y : Subgroup PSL(2, GaloisField 2 3) := X.map e.toMonoidHom with hY
  have hY2 : IsPGroup 2 Y := hX2.map _
  have hYw : ∀ y ∈ Y, w * y * w⁻¹ ∈ Y := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨thetaQuotMulAut L (L.normalizerMonoidHom ⟨b, hb⟩) x, hXinv _ hτ x hx, ?_⟩
    have h1 : e (thetaQuotMulAut L (L.normalizerMonoidHom ⟨b, hb⟩) x) =
        inducedAutHom L e ⟨b, hb⟩ (e x) := by
      rw [inducedAutHom_apply]
      simp [MulAut.congr_apply, compAction]
    change e (thetaQuotMulAut L (L.normalizerMonoidHom ⟨b, hb⟩) x) = w * e x * w⁻¹
    rw [h1, hbw, MulAut.conj_apply]
  have hYbot := psl28_eq_bot_of_normalizes hw3 hw1 hY2 hYw
  apply hX1
  rw [eq_bot_iff]
  intro x hx
  have hy : e x ∈ Y := ⟨x, hx, rfl⟩
  rw [hYbot, Subgroup.mem_bot] at hy
  rw [Subgroup.mem_bot]
  exact (map_eq_one_iff e e.injective).1 hy

end CFSG.RankThree.PartTwo.KFacts
