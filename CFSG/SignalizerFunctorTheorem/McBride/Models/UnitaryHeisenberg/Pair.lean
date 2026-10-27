module

public import CFSG.SignalizerFunctorTheorem.NearModels.Unitary.Basic
public import CFSG.ClassicalGroups.UnitaryFlag.WittBasis
public import CFSG.SignalizerFunctorTheorem.McBride.Models.UnitaryHeisenberg.HeisPair
public import CFSG.SignalizerFunctorTheorem.McBride.Models.UnitaryHeisenberg.Matrix

public section

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag Matrix
open CFSG.SignalizerFunctorTheorem.NearModels.UnitaryAut
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.UnitaryHeisenberg

section Field

variable {p : ℕ} {K : Type*} [Field K]

theorem two_pow_mod_three_of_odd (hp : Odd p) : 2 ^ p % 3 = 2 := by
  obtain ⟨k, rfl⟩ := hp
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem exists_cube_root (h : UnitaryFieldData 2 p K) : ∃ ω : K, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  have := h.finite
  have h3 : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, h.card, pow_mul]
    have h' := Nat.sub_dvd_pow_sub_pow 4 1 p
    norm_num at h' ⊢
    exact h'
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3
  refine ⟨x, ?_, ?_⟩
  · have := pow_orderOf_eq_one x
    rw [hx] at this
    simpa using congrArg Units.val this
  · intro h1
    have : x = 1 := Units.ext h1
    rw [this, orderOf_one] at hx
    omega

theorem bar_mul_self_eq_one (h : UnitaryFieldData 2 p K) (hp : Odd p) {ω : K} (hω : ω ^ 3 = 1) :
    h.bar ω * ω = 1 := by
  rw [UnitaryFieldData.bar_apply, ← pow_succ, pow_eq_pow_mod _ hω, Nat.add_mod,
    two_pow_mod_three_of_odd hp]
  simp

theorem conj_inv_mul_self (σ : K →+* K) (J O Oi : Matrix (Fin 3) (Fin 3) K)
    (hO : (O.map σ)ᵀ * J * O = 1) (hOi : O * Oi = 1) : (Oi.map σ)ᵀ * Oi = J := by
  calc (Oi.map σ)ᵀ * Oi = (Oi.map σ)ᵀ * ((O.map σ)ᵀ * J * O) * Oi := by
        rw [hO, Matrix.mul_one]
    _ = ((O * Oi).map σ)ᵀ * J * (O * Oi) := by
        simp [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = J := by rw [hOi]; simp

theorem unitary_conj (σ : K →+* K) (J O Oi B : Matrix (Fin 3) (Fin 3) K)
    (hO : (O.map σ)ᵀ * J * O = 1) (hOi : O * Oi = 1) (hB : (B.map σ)ᵀ * B = 1) :
    ((O * B * Oi).map σ)ᵀ * J * (O * B * Oi) = J := by
  calc ((O * B * Oi).map σ)ᵀ * J * (O * B * Oi)
      = (Oi.map σ)ᵀ * ((B.map σ)ᵀ * ((O.map σ)ᵀ * J * O) * B) * Oi := by
        simp [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = (Oi.map σ)ᵀ * Oi := by rw [hO, Matrix.mul_one, hB, Matrix.mul_one]
    _ = J := conj_inv_mul_self σ J O Oi hO hOi

theorem unitary_of_conj_isometry (σ : K →+* K) (J O Oi G : Matrix (Fin 3) (Fin 3) K)
    (hO : (O.map σ)ᵀ * J * O = 1) (hOi : O * Oi = 1) (hG : (G.map σ)ᵀ * J * G = J) :
    ((Oi * G * O).map σ)ᵀ * (Oi * G * O) = 1 := by
  calc ((Oi * G * O).map σ)ᵀ * (Oi * G * O)
      = (O.map σ)ᵀ * ((G.map σ)ᵀ * ((Oi.map σ)ᵀ * Oi) * G) * O := by
        simp [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [conj_inv_mul_self σ J O Oi hO hOi, hG, hO]

theorem pow_eq_one_of_diag_unitary (h : UnitaryFieldData 2 p K) {A : Matrix (Fin 3) (Fin 3) K}
    (hd : ∀ i j, i ≠ j → A i j = 0) (hA : (A.map h.bar)ᵀ * A = 1) : A ^ (2 ^ p + 1) = 1 := by
  have hA' : A = Matrix.diagonal (fun i => A i i) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · rw [hd i j hij, Matrix.diagonal_apply_ne _ hij]
  have hunit : ∀ i, A i i ^ (2 ^ p + 1) = 1 := by
    intro i
    have h1 : ((A.map h.bar)ᵀ * A) i i = h.bar (A i i) * A i i := by
      rw [Matrix.mul_apply, Finset.sum_eq_single i]
      · simp
      · intro k _ hk
        simp [hd k i hk]
      · simp
    rw [hA, Matrix.one_apply_eq, UnitaryFieldData.bar_apply, ← pow_succ] at h1
    exact h1.symm
  calc A ^ (2 ^ p + 1) = (Matrix.diagonal (fun i => A i i)) ^ (2 ^ p + 1) := by rw [← hA']
    _ = Matrix.diagonal (fun i => A i i ^ (2 ^ p + 1)) := Matrix.diagonal_pow _ _
    _ = 1 := by simp [hunit]

theorem exists_frame (h : UnitaryFieldData 2 p K) :
    ∃ O : GL (Fin 3) K,
      ((O : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * antidiagGram K *
        (O : Matrix (Fin 3) (Fin 3) K) = 1 := by
  obtain ⟨c, hc⟩ := exists_add_bar_eq_neg_one h
  have := h.charP
  rw [CharTwo.neg_eq] at hc
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero _ 2
  set Om : Matrix (Fin 3) (Fin 3) K := !![1, 0, 1; 0, 1, 0; c, 0, h.bar c] with hOm
  have hOH : (Om.map h.bar)ᵀ * antidiagGram K * Om = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hOm, antidiagGram, Matrix.mul_apply, Fin.sum_univ_three, h.bar_bar]
    all_goals first | linear_combination hc | linear_combination (h.bar c) * h2 |
      linear_combination c * h2
  have hOi : Om * ((Om.map h.bar)ᵀ * antidiagGram K) = 1 := by
    apply mul_eq_one_comm.mp
    exact hOH
  exact ⟨⟨Om, (Om.map h.bar)ᵀ * antidiagGram K, hOi, hOH⟩, hOH⟩

end Field


section GLPair

variable {K : Type*} [Field K]

@[expose] noncomputable def aGL {ω : K} (hω : ω ^ 3 = 1) : GL (Fin 3) K :=
  GeneralLinearGroup.mkOfDetNeZero (aMat ω) (by rw [det_aMat hω]; exact one_ne_zero)

@[expose] noncomputable def bGL : GL (Fin 3) K :=
  GeneralLinearGroup.mkOfDetNeZero bMat (by rw [det_bMat]; exact one_ne_zero)

@[expose] noncomputable def ζGL {ω : K} (hω : ω ^ 3 = 1) : GL (Fin 3) K :=
  GeneralLinearGroup.scalar (Fin 3) (Units.mk0 ω (ne_zero_of_pow_three hω))

theorem coe_aGL {ω : K} (hω : ω ^ 3 = 1) : (aGL hω : Matrix (Fin 3) (Fin 3) K) = aMat ω := rfl

theorem coe_bGL : (bGL : GL (Fin 3) K) = (bMat : Matrix (Fin 3) (Fin 3) K) := rfl

theorem coe_ζGL {ω : K} (hω : ω ^ 3 = 1) : (ζGL hω : Matrix (Fin 3) (Fin 3) K) = ω • 1 := by
  simp [ζGL, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem isHeisPair_GL {ω : K} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    IsHeisPair (aGL hω) bGL (ζGL hω) where
  a_pow := Units.ext (by rw [Units.val_pow_eq_pow_val, coe_aGL, aMat_pow_three hω]; rfl)
  b_pow := Units.ext (by rw [Units.val_pow_eq_pow_val]; exact bMat_pow_three)
  ζ_pow := Units.ext (by
    rw [Units.val_pow_eq_pow_val, coe_ζGL, smul_pow, one_pow, hω, one_smul]; rfl)
  ζ_ne := by
    intro h
    apply hω1
    have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) h
    simpa [coe_ζGL] using this
  ζ_central := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨_, rfl⟩
  ab := Units.ext (by
    simp only [Units.val_mul, coe_aGL, coe_bGL, coe_ζGL]
    rw [aMat_mul_bMat hω, smul_mul_assoc, one_mul])

theorem one_add_add_sq_eq_zero {ω : K} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) : 1 + ω + ω ^ 2 = 0 := by
  have h : (ω - 1) * (1 + ω + ω ^ 2) = 0 := by linear_combination hω
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (sub_eq_zero.mp h) hω1
  · exact h

theorem mem_zpowers_ζGL_of_scalar {ω : K} (hω : ω ^ 3 = 1) (hω1 : ω ≠ 1) {g : GL (Fin 3) K}
    {c : K} (hg : (g : Matrix (Fin 3) (Fin 3) K) = c • 1)
    (hdet : (g : Matrix (Fin 3) (Fin 3) K).det = 1) : g ∈ Subgroup.zpowers (ζGL hω) := by
  have hc : c ^ 3 = 1 := by simpa [hg, Matrix.det_smul] using hdet
  have hs := one_add_add_sq_eq_zero hω hω1
  have hprod : (c - 1) * (c - ω) * (c - ω ^ 2) = 0 := by
    linear_combination hc + (c - c ^ 2) * hs + (c - 1) * hω
  have hcases : c = 1 ∨ c = ω ∨ c = ω ^ 2 := by
    rcases mul_eq_zero.mp hprod with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (Or.inl (sub_eq_zero.mp h))
    · exact Or.inr (Or.inr (sub_eq_zero.mp h))
  rcases hcases with rfl | rfl | rfl
  · have : g = 1 := Units.ext (by rw [hg]; simp)
    rw [this]; exact one_mem _
  · have : g = ζGL hω := Units.ext (by rw [hg, coe_ζGL])
    rw [this]; exact Subgroup.mem_zpowers _
  · have : g = ζGL hω ^ 2 := Units.ext (by
      rw [hg, Units.val_pow_eq_pow_val, coe_ζGL, smul_pow, one_pow])
    rw [this]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

end GLPair

section Helpers

theorem mem_zpowers_of_coe {G : Type*} [Group G] {H : Subgroup G} {z g : H}
    (h : (g : G) ∈ Subgroup.zpowers (z : G)) : g ∈ Subgroup.zpowers z := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, Subtype.ext (by simpa using hn)⟩

end Helpers

section Pair

variable {p : ℕ} {K : Type*} [Field K]

theorem exists_pair_SU3_pow (h : UnitaryFieldData 2 p K) (hp : Odd p) :
    ∃ a b ζ : gramSU h (antidiagGram K), IsHeisPair a b ζ ∧
      (∀ g : gramSU h (antidiagGram K),
        (g : GL (Fin 3) K) ∈ Subgroup.center (GL (Fin 3) K) ↔ g ∈ Subgroup.zpowers ζ) ∧
      (∀ g : gramSU h (antidiagGram K), Commute g a → Commute g b → g ∈ Subgroup.zpowers ζ) ∧
      (∀ x y : gramSU h (antidiagGram K), Commute x a → Commute y b → Commute x y →
        x ∈ Subgroup.zpowers ζ ∨ y ∈ Subgroup.zpowers ζ) ∧
      (∀ g : gramSU h (antidiagGram K), Commute g a → g ^ (2 ^ p + 1) = 1) := by
  obtain ⟨ω, hω3, hω1⟩ := exists_cube_root h
  have hbar : h.bar ω * ω = 1 := bar_mul_self_eq_one h hp hω3
  obtain ⟨O, hO⟩ := exists_frame h
  set J := antidiagGram K with hJ
  have hOOi : (O : Matrix (Fin 3) (Fin 3) K) * ((O⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hconjmem : ∀ A : GL (Fin 3) K,
      (((A : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * (A : Matrix (Fin 3) (Fin 3) K) = 1) →
      (A : Matrix (Fin 3) (Fin 3) K).det = 1 → O * A * O⁻¹ ∈ gramSU h J := by
    intro A hA hdet
    refine mem_gramSU.mpr ⟨?_, ?_⟩
    · simp only [Units.val_mul]
      exact unitary_conj h.bar J (O : Matrix (Fin 3) (Fin 3) K)
        ((O⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) (A : Matrix (Fin 3) (Fin 3) K)
        hO hOOi hA
    · simp only [Units.val_mul, Matrix.det_mul]
      have := congrArg Matrix.det hOOi
      rw [Matrix.det_mul, Matrix.det_one] at this
      calc _ = (A : Matrix (Fin 3) (Fin 3) K).det * ((O : Matrix (Fin 3) (Fin 3) K).det *
          ((O⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det) := by ring
        _ = _ := by rw [this, mul_one, hdet]
  have haMem : O * aGL hω3 * O⁻¹ ∈ gramSU h J :=
    hconjmem _ (by rw [coe_aGL]; exact aMat_unitary h.bar hbar)
      (by rw [coe_aGL]; exact det_aMat hω3)
  have hbMem : O * bGL * O⁻¹ ∈ gramSU h J :=
    hconjmem _ (by rw [coe_bGL]; exact bMat_unitary h.bar) (by rw [coe_bGL]; exact det_bMat)
  have hζMem : ζGL hω3 ∈ gramSU h J := by
    refine mem_gramSU.mpr ⟨?_, ?_⟩
    · rw [coe_ζGL]
      ext i j
      simp [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, apply_ite h.bar]
      linear_combination J i j * hbar
    · rw [coe_ζGL, Matrix.det_smul]
      simpa using hω3
  have hpair : IsHeisPair (⟨O * aGL hω3 * O⁻¹, haMem⟩ : gramSU h J)
      ⟨O * bGL * O⁻¹, hbMem⟩ ⟨ζGL hω3, hζMem⟩ :=
    ((isHeisPair_GL hω3 hω1).conj O).subgroup (gramSU h J) haMem hbMem hζMem
  have hscal : ∀ g : gramSU h J, ∀ c : K, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = c • 1 →
      g ∈ Subgroup.zpowers (⟨ζGL hω3, hζMem⟩ : gramSU h J) := by
    intro g c hg
    exact mem_zpowers_of_coe (mem_zpowers_ζGL_of_scalar hω3 hω1 hg (mem_gramSU.mp g.2).2)
  have hconjscal : ∀ g : GL (Fin 3) K,
      (∃ c : K, ((O⁻¹ * g * O : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = c • 1) →
      ∃ c : K, (g : Matrix (Fin 3) (Fin 3) K) = c • 1 := by
    rintro g ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have : g = O * (O⁻¹ * g * O) * O⁻¹ := by group
    rw [this]
    simp only [Units.val_mul] at hc ⊢
    rw [show (O⁻¹ : GL (Fin 3) K).val * g.val * O.val = c • 1 from hc]
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hOOi]
  have hcent : ∀ g : gramSU h J, (g : GL (Fin 3) K) ∈ Subgroup.center (GL (Fin 3) K) →
      g ∈ Subgroup.zpowers (⟨ζGL hω3, hζMem⟩ : gramSU h J) := by
    intro g hg
    rw [GeneralLinearGroup.center_eq_range_scalar] at hg
    obtain ⟨u, hu⟩ := hg
    apply hscal g (u : K)
    rw [← hu]
    simp [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  have hmatA : ∀ g : gramSU h J, Commute g ⟨O * aGL hω3 * O⁻¹, haMem⟩ →
      ((O⁻¹ * (g : GL (Fin 3) K) * O : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * aMat ω =
        aMat ω * ((O⁻¹ * (g : GL (Fin 3) K) * O : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro g hg
    have h1 : Commute (O⁻¹ * (g : GL (Fin 3) K) * O) (aGL hω3) :=
      commute_inv_conj (hg.map (gramSU h J).subtype)
    simpa [Units.val_mul, coe_aGL] using congrArg Units.val h1.eq
  have hmatB : ∀ g : gramSU h J, Commute g ⟨O * bGL * O⁻¹, hbMem⟩ →
      ((O⁻¹ * (g : GL (Fin 3) K) * O : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * bMat =
        bMat * ((O⁻¹ * (g : GL (Fin 3) K) * O : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro g hg
    have h1 : Commute (O⁻¹ * (g : GL (Fin 3) K) * O) bGL :=
      commute_inv_conj (hg.map (gramSU h J).subtype)
    simpa [Units.val_mul, coe_bGL] using congrArg Units.val h1.eq
  refine ⟨_, _, _, hpair, ?_, ?_, ?_, ?_⟩
  · intro g
    refine ⟨hcent g, fun hg => ?_⟩
    have : (⟨ζGL hω3, hζMem⟩ : gramSU h J) ∈
        (Subgroup.center (GL (Fin 3) K)).comap (gramSU h J).subtype := by
      show ζGL hω3 ∈ Subgroup.center (GL (Fin 3) K)
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨_, rfl⟩
    exact (Subgroup.zpowers_le.mpr this) hg
  · intro g hga hgb
    obtain ⟨c, hc⟩ := commutant hω3 hω1 (hmatA g hga) (hmatB g hgb)
    obtain ⟨c', hc'⟩ := hconjscal _ ⟨c, hc⟩
    exact hscal g c' hc'
  · intro x y hxa hyb hxy
    have m3 : ((O⁻¹ * (x : GL (Fin 3) K) * O : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((O⁻¹ * (y : GL (Fin 3) K) * O : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((O⁻¹ * (y : GL (Fin 3) K) * O : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((O⁻¹ * (x : GL (Fin 3) K) * O : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      have := (commute_conj_conj (hxy.map (gramSU h J).subtype) O).eq
      simpa [Units.val_mul] using congrArg Units.val this
    by_cases hX : ∃ c : K,
        ((O⁻¹ * (x : GL (Fin 3) K) * O : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = c • 1
    · obtain ⟨c', hc'⟩ := hconjscal _ hX
      exact Or.inl (hscal x c' hc')
    · push Not at hX
      obtain ⟨c, hc⟩ := scalar_of_commute_diag_circulant hω3 hω1 (hmatA x hxa) (hmatB y hyb) m3 hX
      obtain ⟨c', hc'⟩ := hconjscal _ ⟨c, hc⟩
      exact Or.inr (hscal y c' hc')
  · intro g hg
    have hA : (((O⁻¹ * (g : GL (Fin 3) K) * O : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map
        h.bar)ᵀ * ((O⁻¹ * (g : GL (Fin 3) K) * O : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        1 := by
      simp only [Units.val_mul]
      exact unitary_of_conj_isometry h.bar J (O : Matrix (Fin 3) (Fin 3) K)
        ((O⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) hO hOOi (mem_gramSU.mp g.2).1
    have h1 : (O⁻¹ * (g : GL (Fin 3) K) * O) ^ (2 ^ p + 1) = 1 :=
      Units.ext (by
        rw [Units.val_pow_eq_pow_val]
        exact pow_eq_one_of_diag_unitary h (diag_of_commute hω3 hω1 (hmatA g hg)) hA)
    have h2 : (O⁻¹ * (g : GL (Fin 3) K) * O) ^ (2 ^ p + 1) =
        O⁻¹ * (g : GL (Fin 3) K) ^ (2 ^ p + 1) * O := by
      simpa using conj_pow (a := O⁻¹) (b := (g : GL (Fin 3) K)) (i := 2 ^ p + 1)
    rw [h2] at h1
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    calc (g : GL (Fin 3) K) ^ (2 ^ p + 1)
        = O * (O⁻¹ * (g : GL (Fin 3) K) ^ (2 ^ p + 1) * O) * O⁻¹ := by group
      _ = 1 := by rw [h1]; group

theorem exists_pair_SU3 (h : UnitaryFieldData 2 p K) (hp : Odd p) :
    ∃ a b ζ : gramSU h (antidiagGram K), IsHeisPair a b ζ ∧
      (∀ g : gramSU h (antidiagGram K),
        (g : GL (Fin 3) K) ∈ Subgroup.center (GL (Fin 3) K) ↔ g ∈ Subgroup.zpowers ζ) ∧
      (∀ g : gramSU h (antidiagGram K), Commute g a → Commute g b → g ∈ Subgroup.zpowers ζ) ∧
      (∀ x y : gramSU h (antidiagGram K), Commute x a → Commute y b → Commute x y →
        x ∈ Subgroup.zpowers ζ ∨ y ∈ Subgroup.zpowers ζ) := by
  obtain ⟨a, b, ζ, hpair, hcent, hCP, hMU, -⟩ := exists_pair_SU3_pow h hp
  exact ⟨a, b, ζ, hpair, hcent, hCP, hMU⟩

end Pair

end CFSG.SignalizerFunctorTheorem.McBride.UnitaryHeisenberg
