module

public import CFSG.LocalAnalysis.StandardType.GGHalfKGCADefs
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.StandardType

private theorem ggKGCANum_card_field : Nat.card GGKGCF = 2 := by
  rw [show (2 : ℕ) = 2 ^ (1 : ℕ) by norm_num, ← GaloisField.card 2 1 (by norm_num)]

private def ggKGCANum_gl (n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range n, (2 ^ n - 2 ^ i)

private theorem ggKGCANum_card_GL (n : ℕ) :
    Nat.card (Matrix.GeneralLinearGroup (Fin n) GGKGCF) = ggKGCANum_gl n := by
  haveI : Fintype GGKGCF := Fintype.ofFinite GGKGCF
  have hcard : Fintype.card GGKGCF = 2 := by
    rw [Fintype.card_eq_nat_card, ggKGCANum_card_field]
  rw [Matrix.card_GL_field, ggKGCANum_gl,
    Fin.prod_univ_eq_prod_range
      (fun i => Fintype.card GGKGCF ^ n - Fintype.card GGKGCF ^ i) n, hcard]

private theorem ggKGCANum_gl_succ (n : ℕ) :
    ggKGCANum_gl (n + 1) = (2 ^ (n + 1) - 1) * 2 ^ n * ggKGCANum_gl n := by
  unfold ggKGCANum_gl
  rw [Finset.prod_range_succ']
  have h1 : ∀ i ∈ Finset.range n,
      2 ^ (n + 1) - 2 ^ (i + 1) = 2 * (2 ^ n - 2 ^ i) := by
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    have hle : 2 ^ i ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ, pow_succ]
    omega
  rw [Finset.prod_congr rfl h1]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  ring_nf

private theorem ggKGCANum_gl_one_le (n : ℕ) : 1 ≤ ggKGCANum_gl n := by
  rw [ggKGCANum_gl]
  have hpos : 0 < ∏ i ∈ Finset.range n, (2 ^ n - 2 ^ i) :=
    Finset.prod_pos (fun i hi => by
      have hi' : i < n := Finset.mem_range.mp hi
      have hlt : 2 ^ i < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) hi'
      omega)
  omega

private theorem ggKGCANum_gl_le_succ (n : ℕ) :
    ggKGCANum_gl n ≤ ggKGCANum_gl (n + 1) := by
  rw [ggKGCANum_gl_succ]
  have hfac : 1 ≤ (2 ^ (n + 1) - 1) * 2 ^ n := by
    have h1 : 1 ≤ 2 ^ (n + 1) - 1 := by
      have h2 : 2 ≤ 2 ^ (n + 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h2 : 1 ≤ 2 ^ n := Nat.one_le_pow n 2 (by norm_num)
    exact Nat.mul_le_mul h1 h2
  calc ggKGCANum_gl n = 1 * ggKGCANum_gl n := (one_mul _).symm
    _ ≤ ((2 ^ (n + 1) - 1) * 2 ^ n) * ggKGCANum_gl n :=
        Nat.mul_le_mul hfac (le_refl _)

private theorem ggKGCANum_gl_lt_succ {n : ℕ} (hn : 1 ≤ n) :
    ggKGCANum_gl n < ggKGCANum_gl (n + 1) := by
  rw [ggKGCANum_gl_succ]
  have hfac : 2 ≤ (2 ^ (n + 1) - 1) * 2 ^ n := by
    have h1 : 1 ≤ 2 ^ (n + 1) - 1 := by
      have h2 : 2 ≤ 2 ^ (n + 1) := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h2 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    exact Nat.mul_le_mul h1 h2
  have hpos : 0 < ggKGCANum_gl n := by
    have := ggKGCANum_gl_one_le n
    omega
  calc ggKGCANum_gl n = 1 * ggKGCANum_gl n := (one_mul _).symm
    _ < 2 * ggKGCANum_gl n := Nat.mul_lt_mul_of_pos_right (by norm_num) hpos
    _ ≤ ((2 ^ (n + 1) - 1) * 2 ^ n) * ggKGCANum_gl n :=
        Nat.mul_le_mul hfac (le_refl _)

private theorem ggKGCANum_gl_lt_of_lt {d m : ℕ} (hd : d < m) (hm : 2 ≤ m) :
    ggKGCANum_gl d < ggKGCANum_gl m := by
  have hle : d ≤ m - 1 := by omega
  have hmono : Monotone ggKGCANum_gl :=
    monotone_nat_of_le_succ ggKGCANum_gl_le_succ
  have h1 : ggKGCANum_gl d ≤ ggKGCANum_gl (m - 1) := hmono hle
  have h2 : ggKGCANum_gl (m - 1) < ggKGCANum_gl ((m - 1) + 1) :=
    ggKGCANum_gl_lt_succ (by omega)
  have hm' : (m - 1) + 1 = m := by omega
  rw [hm'] at h2
  exact Nat.lt_of_le_of_lt h1 h2

private theorem ggKGCANum_gl_lower (n : ℕ) :
    2 ^ (n * (n - 1)) ≤ ggKGCANum_gl n := by
  rcases n with _ | n
  · simp [ggKGCANum_gl]
  · rw [ggKGCANum_gl]
    have h : ∀ i ∈ Finset.range (n + 1), 2 ^ n ≤ 2 ^ (n + 1) - 2 ^ i := by
      intro i hi
      have hi' : i < n + 1 := Finset.mem_range.mp hi
      have hle : 2 ^ i ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      calc 2 ^ n = 2 ^ (n + 1) - 2 ^ n := by rw [pow_succ]; omega
        _ ≤ 2 ^ (n + 1) - 2 ^ i := Nat.sub_le_sub_left hle _
    calc 2 ^ ((n + 1) * ((n + 1) - 1)) = (2 ^ n) ^ (n + 1) := by
          rw [show (n + 1) - 1 = n by omega, Nat.mul_comm, ← pow_mul]
      _ = ∏ _i ∈ Finset.range (n + 1), 2 ^ n := by
          rw [Finset.prod_const, Finset.card_range]
      _ ≤ ∏ i ∈ Finset.range (n + 1), (2 ^ (n + 1) - 2 ^ i) :=
          Finset.prod_le_prod h

private theorem ggKGCANum_arith {m r : ℕ} (hm : 7 ≤ m) (hr : 2 * r ≤ m + 2) :
    2 * r ^ 2 < m * (m - 1) := by
  have h1 : 4 * r ^ 2 ≤ (m + 2) ^ 2 := by
    have := Nat.pow_le_pow_left hr 2
    nlinarith [this]
  have h2 : (m + 2) ^ 2 < 2 * (m * (m - 1)) := by
    have hpoly : (0 : ℤ) < (m : ℤ) ^ 2 - 6 * m - 4 := by
      have h := mul_nonneg (show (0 : ℤ) ≤ (m : ℤ) - 7 by omega)
        (show (0 : ℤ) ≤ (m : ℤ) + 1 by omega)
      nlinarith [h]
    have hm1 : 1 ≤ m := by omega
    zify [hm1]
    nlinarith [hpoly]
  have h3 : 2 * (2 * r ^ 2) < 2 * (m * (m - 1)) := by nlinarith [h1, h2]
  nlinarith [h3]

private theorem ggKGCANum_gl_two : ggKGCANum_gl 2 = 6 := by decide

private theorem ggKGCANum_gl_five : ggKGCANum_gl 5 = 9999360 := by decide

private theorem ggKGCANum_gl_six : ggKGCANum_gl 6 = 20158709760 := by decide

theorem ggKGCANum_card_SL_eq_GL (m : ℕ) :
    Nat.card (Matrix.SpecialLinearGroup (Fin m) GGKGCF) =
      Nat.card (Matrix.GeneralLinearGroup (Fin m) GGKGCF) := by
  have hunits : Nat.card GGKGCFˣ = 1 := by
    rw [Nat.card_units, ggKGCANum_card_field]
  haveI : Subsingleton GGKGCFˣ := (Nat.card_eq_one_iff_unique.mp hunits).1
  have hdet : ∀ g : Matrix.GeneralLinearGroup (Fin m) GGKGCF,
      Matrix.GeneralLinearGroup.det g = 1 := fun g => Subsingleton.elim _ _
  have hsurj : Function.Surjective
      (Matrix.SpecialLinearGroup.toGL (n := Fin m) (R := GGKGCF)) := by
    intro g
    rw [← MonoidHom.mem_range, Matrix.SpecialLinearGroup.range_toGL_eq_ker_det,
      MonoidHom.mem_ker]
    exact hdet g
  exact Nat.card_congr
    (Equiv.ofBijective _ ⟨Matrix.SpecialLinearGroup.toGL_injective, hsurj⟩)

theorem ggKGCANum_card_aut {W : Type} [AddCommGroup W] [Module GGKGCF W]
    [FiniteDimensional GGKGCF W] :
    Nat.card (W ≃ₗ[GGKGCF] W) =
      Nat.card (Matrix.GeneralLinearGroup (Fin (Module.finrank GGKGCF W)) GGKGCF) := by
  let d := Module.finrank GGKGCF W
  let b : Module.Basis (Fin d) GGKGCF W := Module.finBasis GGKGCF W
  let e : (W ≃ₗ[GGKGCF] W) ≃* Matrix.GeneralLinearGroup (Fin d) GGKGCF :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv GGKGCF W).symm.trans
      (Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toRingEquiv.toMulEquiv)
  exact Nat.card_congr e.toEquiv

theorem ggKGCANum_card_aut_lt {W : Type} [AddCommGroup W] [Module GGKGCF W]
    [FiniteDimensional GGKGCF W] {m : ℕ} (hm : 2 ≤ m) (hb : Module.finrank GGKGCF W < m) :
    Nat.card (W ≃ₗ[GGKGCF] W) < Nat.card (Matrix.SpecialLinearGroup (Fin m) GGKGCF) := by
  rw [ggKGCANum_card_aut, ggKGCANum_card_SL_eq_GL]
  simp only [ggKGCANum_card_GL]
  exact ggKGCANum_gl_lt_of_lt hb hm

theorem ggKGCANum_card_aut_two {W : Type} [AddCommGroup W] [Module GGKGCF W]
    [FiniteDimensional GGKGCF W] (h : Module.finrank GGKGCF W = 2) :
    Nat.card (W ≃ₗ[GGKGCF] W) = 6 := by
  rw [ggKGCANum_card_aut, h, ggKGCANum_card_GL, ggKGCANum_gl_two]

theorem ggKGCANum_pow_lt {m r : ℕ} (hm : 5 ≤ m) (hr : 2 * r ≤ m + 2) :
    (2 ^ (2 * r)) ^ r < Nat.card (Matrix.SpecialLinearGroup (Fin m) GGKGCF) := by
  rw [ggKGCANum_card_SL_eq_GL, ggKGCANum_card_GL]
  by_cases hm7 : 7 ≤ m
  · have hlt : 2 * r ^ 2 < m * (m - 1) := ggKGCANum_arith hm7 hr
    calc (2 ^ (2 * r)) ^ r = 2 ^ (2 * r ^ 2) := by rw [← pow_mul]; congr 1; ring
      _ < 2 ^ (m * (m - 1)) := Nat.pow_lt_pow_right (by norm_num) hlt
      _ ≤ ggKGCANum_gl m := ggKGCANum_gl_lower m
  · have hm56 : m = 5 ∨ m = 6 := by omega
    rcases hm56 with rfl | rfl
    · have hr3 : r ≤ 3 := by omega
      interval_cases r <;> norm_num [ggKGCANum_gl_five]
    · have hr4 : r ≤ 4 := by omega
      interval_cases r <;> norm_num [ggKGCANum_gl_six]

end CFSG.StandardType

end
