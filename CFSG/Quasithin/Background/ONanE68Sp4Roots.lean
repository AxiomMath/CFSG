module

public import CFSG.Quasithin.Background.ONanE68Sp4Torus
public import CFSG.Quasithin.Background.ONanE68LieFacts
public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisStructure

public section

namespace CFSG.Quasithin

namespace E6

namespace E68Proof

namespace Sp4

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.QuasithinUnique.Setup.X7b CFSG.Quasithin.SteinbergBS

variable {K : Type} [Field K] [CharP K 2]

theorem omegaCenter_eq : omegaCenter (antiUnipotent K) = antiUnipotentCenter K := by
  ext z
  rw [mem_omegaCenter]
  constructor
  · rintro ⟨hz, hc, -⟩
    exact (mem_antiUnipotentCenter_iff_central z).2 ⟨hz, fun h hh => hc h hh⟩
  · intro hz
    refine ⟨antiUnipotentCenter_le hz, fun y hy => antiUnipotentCenter_comm hz hy, ?_⟩
    obtain ⟨b, c, rfl⟩ := hz
    rw [uElt_mul_self]
    simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact uElt_zero_eq_one

theorem card_omegaCenter [Finite K] :
    Nat.card (omegaCenter (antiUnipotent K)) = Nat.card K * Nat.card K := by
  rw [omegaCenter_eq, ← Nat.card_congr (centerEquiv (K := K)).toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_prod]

section Singer

variable [Finite K]

omit [CharP K 2] in
theorem exists_pow_mul_eq {γ : Kˣ} (hγ : ∀ x : Kˣ, x ∈ Subgroup.zpowers γ) {t t' : K} (ht : t ≠ 0)
    (ht' : t' ≠ 0) : ∃ j : ℕ, (γ : K) ^ j * t = t' := by
  obtain ⟨j, hj⟩ := mem_powers_iff_mem_zpowers.2 (hγ (Units.mk0 (t' * t⁻¹) (mul_ne_zero ht'
    (inv_ne_zero ht))))
  refine ⟨j, ?_⟩
  have := congrArg (fun u : Kˣ => (u : K)) hj
  simp only [Units.val_pow_eq_pow_val, Units.val_mk0] at this
  rw [this]
  field_simp

theorem exists_singer_short :
    ∃ x ∈ Subgroup.normalizer (antiUnipotent K : Set (antiSp K)),
      (∀ z ∈ rootLong K, x * z = z * x) ∧
      ∀ z ∈ rootShort K, z ≠ 1 → ∀ w ∈ rootShort K, w ≠ 1 →
        ∃ j : ℕ, x ^ j * z * (x ^ j)⁻¹ = w := by
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Kˣ)
  refine ⟨tElt 1 γ, mem_normalizer_iff_upper.2 (upper_tElt 1 γ), ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    rw [← mul_inv_eq_iff_eq_mul, tElt_conj_uElt]
    simp
  · rintro _ ⟨t, rfl⟩ hz _ ⟨t', rfl⟩ hw
    have ht : t ≠ 0 := fun h => hz (by rw [h]; exact uElt_zero_eq_one)
    have ht' : t' ≠ 0 := fun h => hw (by rw [h]; exact uElt_zero_eq_one)
    obtain ⟨j, hj⟩ := exists_pow_mul_eq hγ ht ht'
    refine ⟨j, ?_⟩
    rw [tElt_pow, tElt_conj_uElt]
    simp [hj]

theorem exists_singer_long :
    ∃ x ∈ Subgroup.normalizer (antiUnipotent K : Set (antiSp K)),
      (∀ z ∈ rootShort K, x * z = z * x) ∧
      ∀ z ∈ rootLong K, z ≠ 1 → ∀ w ∈ rootLong K, w ≠ 1 →
        ∃ j : ℕ, x ^ j * z * (x ^ j)⁻¹ = w := by
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := Kˣ)
  obtain ⟨ρ, hρ⟩ := CFSG.RankThree.PartOne.KCRootAxis.exists_sq_eq (γ : K)
  have hρ0 : ρ ≠ 0 := fun h => γ.ne_zero (by rw [← hρ, h]; ring)
  refine ⟨tElt (Units.mk0 ρ hρ0) (Units.mk0 ρ hρ0)⁻¹,
    mem_normalizer_iff_upper.2 (upper_tElt _ _), ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    rw [← mul_inv_eq_iff_eq_mul, tElt_conj_uElt]
    simp [hρ0]
  · rintro _ ⟨t, rfl⟩ hz _ ⟨t', rfl⟩ hw
    have ht : t ≠ 0 := fun h => hz (by rw [h]; exact uElt_zero_eq_one)
    have ht' : t' ≠ 0 := fun h => hw (by rw [h]; exact uElt_zero_eq_one)
    obtain ⟨j, hj⟩ := exists_pow_mul_eq hγ ht ht'
    refine ⟨j, ?_⟩
    rw [tElt_pow, tElt_conj_uElt]
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0, inv_pow, Units.val_inv_eq_inv_val,
      mul_zero, inv_inv]
    have e2 : (ρ ^ j) ^ 2 = (γ : K) ^ j := by rw [← hρ, ← pow_mul, ← pow_mul, mul_comm]
    rw [e2, hj]

end Singer

section Automizer

open CFSG.RankThree.PartOne.KCRootAxis (mat mat_mul mat_one)

@[expose] def nShort : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0]

@[expose] def nLong : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0; 0, 0, 0, 0]

theorem mat_uElt_short (t : K) : mat (uElt (0 : K) t 0 0) = 1 + t • nShort := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mat, glMat_uElt, uMat, nShort]

theorem mat_uElt_long (t : K) : mat (uElt (0 : K) 0 t 0) = 1 + t • nLong := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mat, glMat_uElt, uMat, nLong]

omit [CharP K 2] in
theorem conj_scalar {N : Matrix (Fin 4) (Fin 4) K} {f : K → antiSp K}
    (hf : ∀ t, mat (f t) = 1 + t • N) {y : antiSp K} {κ : K} (hκ : y * f 1 * y⁻¹ = f κ)
    (t : K) : y * f t * y⁻¹ = f (κ * t) := by
  apply CFSG.RankThree.PartOne.KCRootAxis.mat_ext
  have hYY : mat y * mat y⁻¹ = 1 := by rw [← mat_mul, mul_inv_cancel, mat_one]
  have h1 := congrArg mat hκ
  rw [mat_mul, mat_mul, hf, hf, one_smul] at h1
  have key : mat y * N * mat y⁻¹ = κ • N := by
    have h2 : mat y * (1 + N) * mat y⁻¹ = 1 + mat y * N * mat y⁻¹ := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hYY]
    rw [h2] at h1
    exact add_left_cancel h1
  rw [mat_mul, mat_mul, hf, hf, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hYY,
    Matrix.mul_smul, Matrix.smul_mul, key, smul_smul, mul_comm]

omit [CharP K 2] in
theorem exists_conj_scalar {N : Matrix (Fin 4) (Fin 4) K} {f : K → antiSp K}
    {S : Subgroup (antiSp K)}
    (hS : ∀ x, x ∈ S ↔ ∃ t, x = f t) (hf : ∀ t, mat (f t) = 1 + t • N) (hf0 : f 0 = 1)
    (hf1 : f 1 ≠ 1) {y : antiSp K} (hy : y ∈ Subgroup.normalizer (S : Set (antiSp K))) :
    ∃ κ : K, κ ≠ 0 ∧ ∀ t, y * f t * y⁻¹ = f (κ * t) := by
  obtain ⟨κ, hκ⟩ := (hS _).1 ((Subgroup.mem_normalizer_iff.1 hy (f 1)).1 ((hS _).2 ⟨1, rfl⟩))
  refine ⟨κ, fun h0 => hf1 ?_, conj_scalar hf hκ⟩
  rw [h0, hf0] at hκ
  have : f 1 = y⁻¹ * 1 * y := by rw [← hκ]; group
  rw [this]
  group

theorem uElt_short_ne_one : uElt (0 : K) 1 0 0 ≠ 1 := fun h => by
  rw [← uElt_zero_eq_one] at h
  exact one_ne_zero (uElt_inj h).2.1

theorem uElt_long_ne_one : uElt (0 : K) 0 1 0 ≠ 1 := fun h => by
  rw [← uElt_zero_eq_one] at h
  exact one_ne_zero (uElt_inj h).2.2.1

theorem exists_torus_conj_short {y : antiSp K}
    (hy : y ∈ Subgroup.normalizer (rootShort K : Set (antiSp K))) :
    ∃ b ∈ Subgroup.normalizer (antiUnipotent K : Set (antiSp K)),
      ∀ z ∈ rootShort K, y * z * y⁻¹ = b * z * b⁻¹ := by
  obtain ⟨κ, hκ0, hκ⟩ := exists_conj_scalar (S := rootShort K) (f := fun t => uElt (0 : K) t 0 0)
    (N := nShort) (fun x => ⟨fun ⟨t, h⟩ => ⟨t, h⟩, fun ⟨t, h⟩ => ⟨t, h⟩⟩) mat_uElt_short
    uElt_zero_eq_one uElt_short_ne_one hy
  refine ⟨tElt (Units.mk0 κ hκ0) 1, mem_normalizer_iff_upper.2 (upper_tElt _ _), ?_⟩
  rintro _ ⟨t, rfl⟩
  rw [hκ t, tElt_conj_uElt]
  simp

theorem exists_torus_conj_long [Finite K] {y : antiSp K}
    (hy : y ∈ Subgroup.normalizer (rootLong K : Set (antiSp K))) :
    ∃ b ∈ Subgroup.normalizer (antiUnipotent K : Set (antiSp K)),
      ∀ z ∈ rootLong K, y * z * y⁻¹ = b * z * b⁻¹ := by
  obtain ⟨κ, hκ0, hκ⟩ := exists_conj_scalar (S := rootLong K) (f := fun t => uElt (0 : K) 0 t 0)
    (N := nLong) (fun x => ⟨fun ⟨t, h⟩ => ⟨t, h⟩, fun ⟨t, h⟩ => ⟨t, h⟩⟩) mat_uElt_long
    uElt_zero_eq_one uElt_long_ne_one hy
  obtain ⟨ρ, hρ⟩ := CFSG.RankThree.PartOne.KCRootAxis.exists_sq_eq κ
  have hρ0 : ρ ≠ 0 := fun h => hκ0 (by rw [← hρ, h]; ring)
  refine ⟨tElt (Units.mk0 ρ hρ0) 1, mem_normalizer_iff_upper.2 (upper_tElt _ _), ?_⟩
  rintro _ ⟨t, rfl⟩
  rw [hκ t, tElt_conj_uElt]
  simp [hρ]

end Automizer

section Perm

open CFSG.RankThree.PartOne.KCRootAxis (mat mat_mul mat_one)

@[expose] def pMat1 : Matrix (Fin 4) (Fin 4) K :=
  !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]

@[expose] def pMat2 : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1]

omit [CharP K 2] in
theorem pMat1_mul_self : pMat1 * pMat1 = (1 : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pMat1, Matrix.mul_apply, Fin.sum_univ_four]

omit [CharP K 2] in
theorem pMat2_mul_self : pMat2 * pMat2 = (1 : Matrix (Fin 4) (Fin 4) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pMat2, Matrix.mul_apply, Fin.sum_univ_four]

omit [CharP K 2] in
theorem pMat1_mem : (pMat1 : Matrix (Fin 4) (Fin 4) K)ᵀ * minorJ K * pMat1 = minorJ K := by
  ext k j
  rw [transpose_mul_minorJ_mul_apply, minorJ_apply]
  fin_cases k <;> fin_cases j <;> simp [pMat1]

omit [CharP K 2] in
theorem pMat2_mem : (pMat2 : Matrix (Fin 4) (Fin 4) K)ᵀ * minorJ K * pMat2 = minorJ K := by
  ext k j
  rw [transpose_mul_minorJ_mul_apply, minorJ_apply]
  fin_cases k <;> fin_cases j <;> simp [pMat2]

@[expose] def pElt1 : antiSp K :=
  ⟨⟨pMat1, pMat1, pMat1_mul_self, pMat1_mul_self⟩, pMat1_mem⟩

@[expose] def pElt2 : antiSp K :=
  ⟨⟨pMat2, pMat2, pMat2_mul_self, pMat2_mul_self⟩, pMat2_mem⟩

omit [CharP K 2] in
theorem mat_pElt1 : mat (pElt1 : antiSp K) = pMat1 := rfl

omit [CharP K 2] in
theorem mat_pElt2 : mat (pElt2 : antiSp K) = pMat2 := rfl

theorem pElt1_comm (t : K) : uElt (0 : K) t 0 0 * pElt1 = pElt1 * uElt 0 t 0 0 := by
  apply CFSG.RankThree.PartOne.KCRootAxis.mat_ext
  rw [mat_mul, mat_mul, mat_pElt1, mat_uElt_short]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pMat1, nShort, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

theorem pElt2_comm (t : K) : uElt (0 : K) 0 t 0 * pElt2 = pElt2 * uElt 0 0 t 0 := by
  apply CFSG.RankThree.PartOne.KCRootAxis.mat_ext
  rw [mat_mul, mat_mul, mat_pElt2, mat_uElt_long]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pMat2, nLong, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply]

theorem not_centralizer_short_le :
    ¬ Subgroup.centralizer (rootShort K : Set (antiSp K)) ≤
      Subgroup.normalizer (antiUnipotent K : Set (antiSp K)) := by
  intro h
  have hc : pElt1 ∈ Subgroup.centralizer (rootShort K : Set (antiSp K)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨t, rfl⟩
    exact pElt1_comm t
  have hu := mem_normalizer_iff_upper.1 (h hc) 1 0 (by decide)
  simp [mat_pElt1, pMat1] at hu

theorem not_centralizer_long_le :
    ¬ Subgroup.centralizer (rootLong K : Set (antiSp K)) ≤
      Subgroup.normalizer (antiUnipotent K : Set (antiSp K)) := by
  intro h
  have hc : pElt2 ∈ Subgroup.centralizer (rootLong K : Set (antiSp K)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨t, rfl⟩
    exact pElt2_comm t
  have hu := mem_normalizer_iff_upper.1 (h hc) 2 1 (by decide)
  simp [mat_pElt2, pMat2] at hu

end Perm

theorem centralizer_omegaCenter_le :
    Subgroup.centralizer (omegaCenter (antiUnipotent K) : Set (antiSp K)) ≤
      Subgroup.normalizer (antiUnipotent K : Set (antiSp K)) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff] at hg
  have h1 := hg (uElt 0 0 1 0) (by rw [omegaCenter_eq]; exact ⟨0, 1, rfl⟩)
  have h2 := hg (uElt 0 1 0 0) (by rw [omegaCenter_eq]; exact ⟨1, 0, rfl⟩)
  have m1 := congrArg CFSG.RankThree.PartOne.KCRootAxis.mat h1
  have m2 := congrArg CFSG.RankThree.PartOne.KCRootAxis.mat h2
  rw [CFSG.RankThree.PartOne.KCRootAxis.mat_mul, CFSG.RankThree.PartOne.KCRootAxis.mat_mul,
    mat_uElt_long] at m1
  rw [CFSG.RankThree.PartOne.KCRootAxis.mat_mul, CFSG.RankThree.PartOne.KCRootAxis.mat_mul,
    mat_uElt_short] at m2
  rw [mem_normalizer_iff_upper]
  have e10 := congrFun (congrFun m1 1) 3
  have e20 := congrFun (congrFun m1 2) 3
  have e30 := congrFun (congrFun m1 3) 3
  have e31 := congrFun (congrFun m1 0) 1
  have e32 := congrFun (congrFun m1 0) 2
  have e21 := congrFun (congrFun m2 2) 3
  simp [nLong, Matrix.mul_apply, Fin.sum_univ_four, Matrix.add_apply] at e10 e20 e30 e31 e32
  simp [nShort, Matrix.mul_apply, Fin.sum_univ_four, Matrix.add_apply] at e21
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simp_all




end Sp4

end E68Proof

end E6

end CFSG.Quasithin
