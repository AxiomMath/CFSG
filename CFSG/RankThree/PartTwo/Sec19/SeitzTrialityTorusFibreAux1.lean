module

public import CFSG.RankThree.PartOne.D4RC.RxFrame

public section

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne
  CFSG.RankThree.Lattice CFSG.RankThree.Chevalley.TrialityFold
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartOne.D4RC
open CFSG.RankThree.Classical2 (fixSubgroup unitarySet)
open scoped Matrix MatrixGroups

namespace CFSG.RankThree.PartTwo.Sec19

theorem rcfa_scalar_sl {K' : Type} [Field K'] (u : K') (hu : u ^ 3 = 1) :
    ∃ z : Matrix.SpecialLinearGroup (Fin 3) K', (z : Matrix (Fin 3) (Fin 3) K') = u • 1 :=
  ⟨⟨u • 1, by rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, hu]⟩, rfl⟩

theorem rcfa_map_scalar {K' L' : Type} [Field K'] [Field L'] (f : K' →+* L') (u : K') :
    (u • (1 : Matrix (Fin 3) (Fin 3) K')).map f = f u • (1 : Matrix (Fin 3) (Fin 3) L') := by
  ext i j
  by_cases h : i = j
  · subst h
    simp
  · simp [Matrix.one_apply_ne h]

theorem rcfa_map_pow_scalar {K' : Type} [Field K'] (q : ℕ) (hq : q ≠ 0) (u : K') :
    (u • (1 : Matrix (Fin 3) (Fin 3) K')).map (· ^ q) =
      (u ^ q) • (1 : Matrix (Fin 3) (Fin 3) K') := by
  ext i j
  by_cases h : i = j
  · subst h
    simp
  · simp [Matrix.one_apply_ne h, zero_pow hq]

theorem rcfa_scalar_pow {K' : Type} [Field K'] (u : K') (k : ℕ) :
    (u • (1 : Matrix (Fin 3) (Fin 3) K')) ^ k = (u ^ k) • (1 : Matrix (Fin 3) (Fin 3) K') := by
  rw [smul_pow, one_pow]

theorem rcfa_scalar_central {K' : Type} [Field K'] (u : K')
    (z : Matrix.SpecialLinearGroup (Fin 3) K') (hz : (z : Matrix (Fin 3) (Fin 3) K') = u • 1)
    (g : Matrix.SpecialLinearGroup (Fin 3) K') : g * z = z * g := by
  apply Subtype.ext
  simp [Matrix.SpecialLinearGroup.coe_mul, hz, Matrix.mul_smul, Matrix.smul_mul]

theorem rcfa_scalar_pow_eq_one {K' : Type} [Field K'] (u : K')
    (z : Matrix.SpecialLinearGroup (Fin 3) K') (hz : (z : Matrix (Fin 3) (Fin 3) K') = u • 1)
    (hu : u ^ 3 = 1) : z ^ 3 = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, hz, rcfa_scalar_pow, hu, one_smul,
    Matrix.SpecialLinearGroup.coe_one]

theorem rcfa_scalar_ne_one {K' : Type} [Field K'] (u : K') (hu : u ≠ 1)
    (z : Matrix.SpecialLinearGroup (Fin 3) K') (hz : (z : Matrix (Fin 3) (Fin 3) K') = u • 1) :
    z ≠ 1 := by
  intro h
  apply hu
  have h0 : (z : Matrix (Fin 3) (Fin 3) K') = (1 : Matrix (Fin 3) (Fin 3) K') := by
    rw [h, Matrix.SpecialLinearGroup.coe_one]
  have h1 := congrFun (congrFun h0 0) 0
  simpa [hz] using h1

theorem rcfa_unitary_scalar {K' : Type} [Field K'] (q : ℕ) (hq : q ≠ 0) (u : K')
    (hu : u ^ q * u = 1) :
    ((u • (1 : Matrix (Fin 3) (Fin 3) K')).map (· ^ q))ᵀ * (u • (1 : Matrix (Fin 3) (Fin 3) K')) =
      1 := by
  rw [rcfa_map_pow_scalar q hq u, Matrix.transpose_smul, Matrix.transpose_one]
  simp only [Matrix.smul_mul, Matrix.one_mul, smul_smul, hu, one_smul]

theorem rcfa_cube_root {K' : Type} [Field K'] [Finite K'] (h : 3 ∣ Nat.card K' - 1) :
    ∃ x : K', x ^ 3 = 1 ∧ x ≠ 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ∣ Nat.card K'ˣ := by rw [Nat.card_units]; exact h
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  have hg3 : g ^ 3 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  refine ⟨(g : K'), ?_, ?_⟩
  · rw [← Units.val_pow_eq_pow_val, hg3, Units.val_one]
  · intro h1
    have hg1 : g = 1 := Units.ext h1
    rw [hg1, orderOf_one] at hg
    norm_num at hg

section Aux1


variable {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

theorem rcfa_central_order_three {ε : ℤ} {p : ℕ} {L : Type} [Field L] [Algebra X L]
    [IsAlgClosure X L] [CharP L 2] {F : RclFrame 2 n X σ ε p L} {i : Fin 4} (D : RclAlgData F i)
    (h3 : (3 : ℤ) ∣ ((2 ^ n : ℕ) : ℤ) - ε) :
    ∃ z : Matrix.SpecialLinearGroup (Fin 3) L, z ∈ fixSubgroup D.Φ' ∧
      (∀ g : Matrix.SpecialLinearGroup (Fin 3) L, g * z = z * g) ∧ z ^ 3 = 1 ∧ z ≠ 1 := by
  rcases F.hε with h1 | h1
  ·
    have h3' : (3 : ℤ) ∣ ((2 ^ n : ℕ) : ℤ) - 1 := by rw [h1] at h3; exact h3
    have hdiv : 3 ∣ 2 ^ n - 1 := by omega
    have hcard := card_fixSubfield_cube Nat.prime_two F.hf F.hK σ F.hσ
    obtain ⟨x, hx3, hx1⟩ := rcfa_cube_root (K' := ↥(CFSG.LieType.Chevalley.fixSubfield σ))
      (by rw [hcard]; exact hdiv)
    have hx3' : (algebraMap (↥(CFSG.LieType.Chevalley.fixSubfield σ)) L x) ^ 3 = 1 := by
      rw [← map_pow, hx3, map_one]
    have hne : algebraMap (↥(CFSG.LieType.Chevalley.fixSubfield σ)) L x ≠ 1 := fun h =>
      hx1 ((algebraMap (↥(CFSG.LieType.Chevalley.fixSubfield σ)) L).injective
        (by rw [map_one]; exact h))
    obtain ⟨Y, hY⟩ := rcfa_scalar_sl x hx3
    obtain ⟨z, hz⟩ := rcfa_scalar_sl (algebraMap (↥(CFSG.LieType.Chevalley.fixSubfield σ)) L x) hx3'
    have hmapY : Matrix.SpecialLinearGroup.map
        (algebraMap (↥(CFSG.LieType.Chevalley.fixSubfield σ)) L) Y = z := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.map_apply_coe, hY, hz, RingHom.mapMatrix_apply,
        rcfa_map_scalar]
    have hc : ∀ g : Matrix.SpecialLinearGroup (Fin 3) L, g * z = z * g :=
      rcfa_scalar_central _ z hz
    have hmem : z ∈ fixSubgroup D.Φ' := by
      refine (D.split h1 z).2 ⟨Y, ?_⟩
      rw [hmapY, hc D.H, mul_inv_cancel_right]
    exact ⟨z, hmem, hc, rcfa_scalar_pow_eq_one _ z hz hx3', rcfa_scalar_ne_one _ hne z hz⟩
  ·
    have hdiv : 3 ∣ 2 ^ n + 1 := by rw [h1] at h3; omega
    have hq3 : 2 ^ n % 3 = 2 := by omega
    have : IsAlgClosed L := IsAlgClosure.isAlgClosed X
    have hdeg : (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial L).degree = 2 := by
      compute_degree!
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_root (Polynomial.X ^ 2 + Polynomial.X + 1 : Polynomial L)
      (by rw [hdeg]; decide)
    have hw2 : w ^ 2 + w + 1 = 0 := by simpa [Polynomial.IsRoot] using hw
    have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
    have hw3 : w ^ 3 = 1 := by linear_combination (w - 1) * hw2
    have hw1 : w ≠ 1 := by
      intro h
      rw [h] at hw2
      have h10 : (1 : L) = 0 := by linear_combination hw2 - h2
      exact one_ne_zero h10
    obtain ⟨m, hm⟩ := hdiv
    have hw_q1 : w ^ (2 ^ n) * w = 1 := by
      rw [← pow_succ, hm, pow_mul w 3, hw3, one_pow]
    obtain ⟨j, hj⟩ : ∃ j, 2 ^ n = 3 * j + 2 := ⟨2 ^ n / 3, by omega⟩
    have hq2 : (2 ^ n) ^ 2 = 3 * (3 * j ^ 2 + 4 * j + 1) + 1 := by
      rw [hj]; ring
    have hw_q2 : w ^ ((2 ^ n) ^ 2) = w := by
      rw [hq2, pow_succ w, pow_mul w 3, hw3, one_pow, one_mul]
    have hq0 : (2 ^ n) ^ 2 ≠ 0 := by positivity
    have hq0' : 2 ^ n ≠ 0 := by positivity
    obtain ⟨z, hz⟩ := rcfa_scalar_sl w hw3
    have hc : ∀ g : Matrix.SpecialLinearGroup (Fin 3) L, g * z = z * g :=
      rcfa_scalar_central _ z hz
    have hmem : Matrix.SpecialLinearGroup.toGL z ∈ unitarySet (2 ^ n) 3 := by
      have hcoe : (Matrix.SpecialLinearGroup.toGL z : Matrix (Fin 3) (Fin 3) L) = w • 1 := hz
      simp only [unitarySet, Set.mem_setOf_eq, hcoe]
      refine ⟨?_, ?_, rcfa_unitary_scalar (2 ^ n) hq0' w hw_q1⟩
      · intro i j
        by_cases hij : i = j
        · subst hij
          simp [hw_q2]
        · simp [Matrix.one_apply_ne hij, zero_pow hq0]
      · rw [Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, hw3]
    have hconj : D.H * z * D.H⁻¹ = z := by
      rw [hc D.H, mul_inv_cancel_right]
    have heq : Matrix.SpecialLinearGroup.toGL z = Matrix.SpecialLinearGroup.toGL D.H *
        Matrix.SpecialLinearGroup.toGL z * (Matrix.SpecialLinearGroup.toGL D.H)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul, hconj]
    exact ⟨z, (D.unit h1 z).2 ⟨Matrix.SpecialLinearGroup.toGL z, hmem, heq⟩, hc,
      rcfa_scalar_pow_eq_one w z hz hw3, rcfa_scalar_ne_one w hw1 z hz⟩

end Aux1

end CFSG.RankThree.PartTwo.Sec19
