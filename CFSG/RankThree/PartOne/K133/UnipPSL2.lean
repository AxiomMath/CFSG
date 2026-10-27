module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
import Mathlib.LinearAlgebra.Matrix.CharP

public section

namespace CFSG.RankThree.PartOne.K133

open Matrix

variable {F : Type*} [Field F]

theorem sq_eq_trace_smul_sub_det (N : Matrix (Fin 2) (Fin 2) F) :
    N * N = N.trace • N - N.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace, Matrix.det_fin_two] <;> ring

theorem no_anticommute (n11 n12 n21 a b c d ε : F) (h2 : (2 : F) ≠ 0) (hε : ε * ε = 1)
    (hN : n11 * n11 + n12 * n21 = 0) (hdet : a * d - b * c = 1)
    (E1 : 2 * ε * a + 2 * n11 * a + n12 * c + n21 * b = 0)
    (E2 : 2 * ε * b + n12 * (a + d) = 0) (E3 : 2 * ε * c + n21 * (a + d) = 0)
    (E4 : 2 * ε * d - 2 * n11 * d + n21 * b + n12 * c = 0) : False := by
  have hb2 : 2 * b = -(ε * n12 * (a + d)) := by linear_combination ε * E2 - 2 * b * hε
  have hc2 : 2 * c = -(ε * n21 * (a + d)) := by linear_combination ε * E3 - 2 * c * hε
  have had2 : 2 * (a - d) = -(2 * ε * n11 * (a + d)) := by
    linear_combination ε * (E1 - E4) - 2 * (a - d) * hε
  have had : a - d = -(ε * n11 * (a + d)) := by
    apply mul_left_cancel₀ h2
    linear_combination had2
  have hbc : 2 * (n12 * c + n21 * b) = -(2 * ε * n12 * n21 * (a + d)) := by
    linear_combination n12 * hc2 + n21 * hb2
  have hbc' : n12 * c + n21 * b = -(ε * n12 * n21 * (a + d)) := by
    apply mul_left_cancel₀ h2
    linear_combination hbc
  have hτ2 : 2 * (ε * (a + d)) = 0 := by
    linear_combination (E1 + E4) - 2 * n11 * had - 2 * hbc' + 2 * ε * (a + d) * hN
  have hτ : ε * (a + d) = 0 := by
    rcases mul_eq_zero.1 hτ2 with h | h
    · exact absurd h h2
    · exact h
  have hε0 : ε ≠ 0 := by
    intro h
    rw [h, zero_mul] at hε
    exact zero_ne_one hε
  have hτ0 : a + d = 0 := (mul_eq_zero.1 hτ).resolve_left hε0
  have hb0 : b = 0 := by
    have : 2 * b = 0 := by rw [hb2, hτ0]; ring
    exact (mul_eq_zero.1 this).resolve_left h2
  have hc0 : c = 0 := by
    have : 2 * c = 0 := by rw [hc2, hτ0]; ring
    exact (mul_eq_zero.1 this).resolve_left h2
  have hdd : a - d = 0 := by rw [had, hτ0]; ring
  have ha0 : a = 0 := by
    have : 2 * a = 0 := by linear_combination hτ0 + hdd
    exact (mul_eq_zero.1 this).resolve_left h2
  have hd0 : d = 0 := by linear_combination hτ0 - ha0
  rw [ha0, hd0, hb0, hc0] at hdet
  simp at hdet

theorem commutant_disc (n11 n12 n21 a b c d : F) (hN : n11 * n11 + n12 * n21 = 0)
    (hne : ¬ (n11 = 0 ∧ n12 = 0 ∧ n21 = 0)) (F1 : n12 * c = n21 * b)
    (F2 : 2 * n11 * b + n12 * (d - a) = 0) (F3 : n21 * (a - d) = 2 * n11 * c) :
    (a - d) ^ 2 + 4 * b * c = 0 := by
  by_cases h12 : n12 = 0
  · have hn11 : n11 = 0 := by
      have : n11 * n11 = 0 := by simpa [h12] using hN
      exact mul_self_eq_zero.1 this
    have hn21 : n21 ≠ 0 := fun h => hne ⟨hn11, h12, h⟩
    have hb : b = 0 := by
      have : n21 * b = 0 := by simpa [h12] using F1.symm
      exact (mul_eq_zero.1 this).resolve_left hn21
    have hab : a - d = 0 := by
      have : n21 * (a - d) = 0 := by rw [F3, hn11]; ring
      exact (mul_eq_zero.1 this).resolve_left hn21
    rw [hab, hb]
    ring
  · have h12' : n12 ^ 2 ≠ 0 := pow_ne_zero 2 h12
    apply mul_left_cancel₀ h12'
    linear_combination (2 * n11 * b + n12 * (d - a) - 4 * n11 * b) * F2 + 4 * n12 * b * F1 +
      4 * b ^ 2 * hN

theorem sq_eq_zero_of_pow_eq_zero {p : ℕ} (hp : 0 < p) (N : Matrix (Fin 2) (Fin 2) F)
    (hN : N ^ p = 0) (hne : N ≠ 0) : N * N = 0 ∧ N.trace = 0 := by
  have hdet : N.det = 0 := by
    have h1 : N.det ^ p = 0 := by rw [← Matrix.det_pow, hN]; simp
    exact pow_eq_zero_iff hp.ne' |>.1 h1
  have hsq : N * N = N.trace • N := by rw [sq_eq_trace_smul_sub_det, hdet]; simp
  have hpow : ∀ k : ℕ, N ^ (k + 1) = N.trace ^ k • N := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, smul_mul_assoc, hsq, smul_smul, ← pow_succ]
  have h1 : N.trace ^ (p - 1) • N = 0 := by
    rw [← hpow, Nat.sub_add_cancel hp, hN]
  have ht : N.trace = 0 := by
    rcases smul_eq_zero.1 h1 with h | h
    · exact pow_eq_zero_iff (by
        intro h0
        have hp1 : p = 1 := by omega
        subst hp1
        simp at hN
        exact hne hN) |>.1 h
    · exact absurd h hne
  exact ⟨by rw [hsq, ht]; simp, ht⟩

theorem sub_smul_pow_eq_zero {p : ℕ} [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2)
    (X : Matrix (Fin 2) (Fin 2) F) (ε : F) (hε : ε * ε = 1)
    (hX : X ^ p = ε • (1 : Matrix (Fin 2) (Fin 2) F)) :
    (X - ε • (1 : Matrix (Fin 2) (Fin 2) F)) ^ p = 0 := by
  have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  obtain ⟨k, hk⟩ := hpodd
  have hεp : ε ^ p = ε := by
    rw [hk, pow_succ, pow_mul, sq, hε, one_pow, one_mul]
  have h1 : (X - ε • (1 : Matrix (Fin 2) (Fin 2) F)) ^ p =
      X ^ p + ((-ε) • (1 : Matrix (Fin 2) (Fin 2) F)) ^ p := by
    rw [sub_eq_add_neg, ← neg_smul]
    exact add_pow_char_of_commute p (Commute.smul_right (Commute.one_right X) (-ε))
  have hnegp : (-ε) ^ p = -ε := by
    rw [Odd.neg_pow ⟨k, hk⟩, hεp]
  rw [h1, hX, smul_pow, one_pow, hnegp, ← add_smul, add_neg_cancel, zero_smul]

theorem unip_commutant_pow {p : ℕ} [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2)
    (X Y : Matrix (Fin 2) (Fin 2) F) (ε s : F) (hε : ε * ε = 1) (hs : s * s = 1)
    (hdetY : Y.det = 1) (hXp : X ^ p = ε • (1 : Matrix (Fin 2) (Fin 2) F))
    (hXne : X ≠ ε • (1 : Matrix (Fin 2) (Fin 2) F)) (hXY : X * Y = s • (Y * X)) :
    ∃ α : F, α * α = 1 ∧ Y ^ p = α • (1 : Matrix (Fin 2) (Fin 2) F) := by
  have hp : p.Prime := Fact.out
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff F p] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  set N : Matrix (Fin 2) (Fin 2) F := X - ε • 1 with hNdef
  have hNp : N ^ p = 0 := sub_smul_pow_eq_zero hp2 X ε hε hXp
  have hNne : N ≠ 0 := sub_ne_zero.2 hXne
  obtain ⟨hNN, hNtr⟩ := sq_eq_zero_of_pow_eq_zero hp.pos N hNp hNne
  have hXij : ∀ i j, X i j = N i j + ε * (1 : Matrix (Fin 2) (Fin 2) F) i j := fun i j => by
    simp [hNdef]
  have hn22 : N 1 1 = - N 0 0 := by
    have : N 0 0 + N 1 1 = 0 := by simpa [Matrix.trace, Fin.sum_univ_two] using hNtr
    linear_combination this
  have hN00 : N 0 0 * N 0 0 + N 0 1 * N 1 0 = 0 := by
    have := congrFun (congrFun hNN 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have hne : ¬ (N 0 0 = 0 ∧ N 0 1 = 0 ∧ N 1 0 = 0) := by
    rintro ⟨h1, h2', h3⟩
    apply hNne
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h1, h2', h3, hn22]
  have hdetY' : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = 1 := by
    rw [← Matrix.det_fin_two]; exact hdetY
  have hE : ∀ i j, (X * Y) i j = s * (Y * X) i j := fun i j => by
    have := congrFun (congrFun hXY i) j
    simpa using this
  have e00 := hE 0 0
  have e01 := hE 0 1
  have e10 := hE 1 0
  have e11 := hE 1 1
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [Matrix.mul_apply, Fin.sum_univ_two, hXij, Matrix.one_apply_eq, Matrix.one_apply_ne h01,
    Matrix.one_apply_ne h10, mul_one, mul_zero, hn22] at e00 e01 e10 e11
  rcases mul_self_eq_one_iff.1 hs with hs1 | hs1
  ·
    subst hs1
    have F1 : N 0 1 * Y 1 0 = N 1 0 * Y 0 1 := by linear_combination e00
    have F2 : 2 * N 0 0 * Y 0 1 + N 0 1 * (Y 1 1 - Y 0 0) = 0 := by linear_combination e01
    have F3 : N 1 0 * (Y 0 0 - Y 1 1) = 2 * N 0 0 * Y 1 0 := by linear_combination e10
    have hdisc := commutant_disc (N 0 0) (N 0 1) (N 1 0) (Y 0 0) (Y 0 1) (Y 1 0) (Y 1 1) hN00 hne F1
      F2 F3
    set τ : F := Y 0 0 + Y 1 1 with hτ
    have hτ2 : τ * τ = 4 := by
      rw [hτ]; linear_combination hdisc + 4 * hdetY'
    set α : F := τ / 2 with hα
    have hαα : α * α = 1 := by
      rw [hα]; field_simp; linear_combination hτ2
    set M : Matrix (Fin 2) (Fin 2) F := Y - α • 1 with hM
    have h2α : 2 * α = Y 0 0 + Y 1 1 := by rw [hα, hτ]; field_simp
    have hMM : M * M = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hM, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
      · linear_combination (-(Y 0 0)) * h2α + hαα - hdetY'
      · linear_combination (-(Y 0 1)) * h2α
      · linear_combination (-(Y 1 0)) * h2α
      · linear_combination (-(Y 1 1)) * h2α + hαα - hdetY'
    have hM0 : M ^ p = 0 := by
      obtain ⟨k, hk⟩ : ∃ k, p = k + 2 := ⟨p - 2, by have := hp.two_le; omega⟩
      rw [hk, pow_add, pow_two, hMM, mul_zero]
    have hYM : Y = α • (1 : Matrix (Fin 2) (Fin 2) F) + M := by rw [hM]; abel
    have hpodd : Odd p := hp.odd_of_ne_two hp2
    obtain ⟨k, hk⟩ := hpodd
    have hαp : α ^ p = α := by rw [hk, pow_succ, pow_mul, sq, hαα, one_pow, one_mul]
    refine ⟨α, hαα, ?_⟩
    rw [hYM, add_pow_char_of_commute p (Commute.smul_left (Commute.one_left M) α), hM0, add_zero,
      smul_pow, one_pow, hαp]
  ·
    subst hs1
    exfalso
    refine no_anticommute (N 0 0) (N 0 1) (N 1 0) (Y 0 0) (Y 0 1) (Y 1 0) (Y 1 1) ε h2 hε hN00
      hdetY' ?_ ?_ ?_ ?_
    · linear_combination e00
    · linear_combination e01
    · linear_combination e10
    · linear_combination e11

open scoped MatrixGroups

theorem scalar_eq_smul_one (r : F) :
    (Matrix.scalar (Fin 2) r : Matrix (Fin 2) (Fin 2) F) = r • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]

theorem sl2_mem_center_iff (Z : SpecialLinearGroup (Fin 2) F) :
    Z ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) ↔
      ∃ r : F, r * r = 1 ∧ (Z : Matrix (Fin 2) (Fin 2) F) = r • (1 : Matrix (Fin 2) (Fin 2) F) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r, hr, hZ⟩
    refine ⟨r, ?_, ?_⟩
    · rw [Fintype.card_fin] at hr
      rw [← sq]; exact hr
    · rw [← hZ, scalar_eq_smul_one]
  · rintro ⟨r, hr, hZ⟩
    refine ⟨r, ?_, ?_⟩
    · rw [Fintype.card_fin, sq]; exact hr
    · ext1
      rw [hZ, scalar_eq_smul_one]

theorem psl2_centralizer_pow [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2)
    (x y : CFSG.GorensteinWalter.PSL2 F) (hx1 : x ≠ 1) (hxp : x ^ p = 1) (hxy : x * y = y * x) :
    y ^ p = 1 := by
  obtain ⟨X, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨Y, rfl⟩ := QuotientGroup.mk_surjective y
  have hXp : X ^ p ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]; exact hxp
  obtain ⟨ε, hε, hXε⟩ := (sl2_mem_center_iff _).1 hXp
  have hXne : (X : Matrix (Fin 2) (Fin 2) F) ≠ ε • (1 : Matrix (Fin 2) (Fin 2) F) := by
    intro h
    apply hx1
    rw [QuotientGroup.eq_one_iff]
    exact (sl2_mem_center_iff _).2 ⟨ε, hε, h⟩
  have hcomm : X * Y * X⁻¹ * Y⁻¹ ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have : (X : CFSG.GorensteinWalter.PSL2 F) * Y = Y * X := hxy
    rw [this]; group
  obtain ⟨s, hs, hsc⟩ := (sl2_mem_center_iff _).1 hcomm
  have hXY : (X : Matrix (Fin 2) (Fin 2) F) * Y = s • ((Y : Matrix (Fin 2) (Fin 2) F) * X) := by
    have h1 : X * Y = (X * Y * X⁻¹ * Y⁻¹) * (Y * X) := by group
    have h3 : ((X * Y : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
        ((X * Y * X⁻¹ * Y⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          ((Y * X : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, ← h1]
    rw [hsc] at h3
    simp only [Matrix.SpecialLinearGroup.coe_mul, smul_mul_assoc, one_mul] at h3
    exact h3
  have hXp' : (X : Matrix (Fin 2) (Fin 2) F) ^ p = ε • (1 : Matrix (Fin 2) (Fin 2) F) := by
    rw [← Matrix.SpecialLinearGroup.coe_pow]; exact hXε
  obtain ⟨α, hαα, hYp⟩ := unip_commutant_pow hp2 (X : Matrix (Fin 2) (Fin 2) F)
    (Y : Matrix (Fin 2) (Fin 2) F) ε s hε hs (Matrix.SpecialLinearGroup.det_coe Y) hXp' hXne hXY
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact (sl2_mem_center_iff _).2 ⟨α, hαα, by rw [Matrix.SpecialLinearGroup.coe_pow, hYp]⟩

end CFSG.RankThree.PartOne.K133
