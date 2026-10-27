module

public import CFSG.RankThree.PartOne.FOC.CenFactor
public import CFSG.RankThree.PartOne.FOC.ShiftMult
public import CFSG.RankThree.PartOne.KC.EvenUnitaryFiveEigen
public import CFSG.RankThree.PartOne.S11c.SuFiveAut
public import CFSG.RankThree.Native.DerivedGenerators
public import CFSG.RankThree.PartOne.FOC.UnitarySplitAll

public section

namespace CFSG.RankThree.PartOne.FOC

open Matrix CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCUnitary CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCEvenUnitaryFive Polynomial

section Arith

variable {f : ℕ}

theorem two_pow_mod_five (h5 : 5 ∣ 2 ^ f + 1) : 2 ^ f % 5 = 4 := by omega

theorem mod_four_eq_two (h5 : 5 ∣ 2 ^ f + 1) : f % 4 = 2 := by
  have h1 : 2 ^ f % 5 = 4 := two_pow_mod_five h5
  have h2 : 2 ^ f % 5 = 2 ^ (f % 4) % 5 := by
    conv_lhs => rw [← Nat.div_add_mod f 4, pow_add, pow_mul]
    rw [Nat.mul_mod, Nat.pow_mod]
    norm_num
  have h3 : f % 4 < 4 := Nat.mod_lt _ (by norm_num)
  rw [h1] at h2
  interval_cases hr : f % 4
  · norm_num at h2
  · norm_num at h2
  · rfl
  · norm_num at h2

theorem four_le_two_pow (h5 : 5 ∣ 2 ^ f + 1) : 4 ≤ 2 ^ f := by
  have h4 := mod_four_eq_two h5
  have : 2 ≤ f := by omega
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) this

theorem not_two_dvd_succ (h5 : 5 ∣ 2 ^ f + 1) : ¬ 2 ∣ 2 ^ f + 1 := by
  have h4 := mod_four_eq_two h5
  have : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  omega

theorem not_three_dvd_succ (h5 : 5 ∣ 2 ^ f + 1) : ¬ 3 ∣ 2 ^ f + 1 := by
  have h4 := mod_four_eq_two h5
  obtain ⟨k, hk⟩ : ∃ k, f = 2 * k := ⟨f / 2, by omega⟩
  have : 2 ^ f % 3 = 1 := by
    rw [hk, pow_mul, Nat.pow_mod]
    norm_num
  omega

theorem coprime_of_two_le_four (h5 : 5 ∣ 2 ^ f + 1) {m : ℕ} (h2 : 2 ≤ m) (h4 : m ≤ 4) :
    Nat.Coprime m (2 ^ f + 1) := by
  interval_cases m
  · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (not_two_dvd_succ h5)
  · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (not_three_dvd_succ h5)
  · have := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (not_two_dvd_succ h5)
    exact Nat.Coprime.pow_left 2 this

end Arith

section Five

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}


noncomputable abbrev endP (P : GL (Fin 5) K) : Module.End K (Fin 5 → K) :=
  ((Matrix.GeneralLinearGroup.toLin P : LinearMap.GeneralLinearGroup K (Fin 5 → K)) :
    Module.End K (Fin 5 → K))

theorem aeval_endP_eq_zero {P : unit5 h} {c : Kˣ}
    (hP5 : (P : GL (Fin 5) K) ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin 5) c) :
    aeval (endP (P : GL (Fin 5) K)) (X ^ 5 - C (c : K)) = 0 :=
  aeval_toLinU_eq_zero h (x := P) (by rw [Subgroup.coe_pow]; exact hP5)

theorem mult_le_one_of_no_root {P : unit5 h} {c : Kˣ}
    (hP5 : (P : GL (Fin 5) K) ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin 5) c)
    (hb : ¬ ∃ b : K, b ^ 5 = c) (a : primaryFactors (endP (P : GL (Fin 5) K))) :
    primaryMultiplicity (endP (P : GL (Fin 5) K)) (a : K[X]) ≤ 1 := by
  have hirr : Irreducible (X ^ 5 - C (c : K)) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_five (fun b hb' => hb ⟨b, hb'⟩)
  have hmin : minpoly K (endP (P : GL (Fin 5) K)) = X ^ 5 - C (c : K) :=
    (minpoly.eq_of_irreducible_of_monic hirr (aeval_endP_eq_zero hP5)
      (monic_X_pow_sub_C _ (by norm_num))).symm
  obtain ⟨hai, ham, hadvd⟩ := mem_primaryFactors.mp a.2
  have hmonic : (X ^ 5 - C (c : K) : K[X]).Monic := monic_X_pow_sub_C _ (by norm_num)
  have haeq : (a : K[X]) = X ^ 5 - C (c : K) := by
    rw [hmin] at hadvd
    exact eq_of_monic_of_associated ham hmonic (hai.associated_of_dvd hirr hadvd)
  have : Fact (Irreducible (a : K[X])) := ⟨hai⟩
  have h1 := finrank_primaryComponent (x := (endP (P : GL (Fin 5) K))) (a := (a : K[X]))
  have h2 : Module.finrank K (primaryComponent (endP (P : GL (Fin 5) K)) (a : K[X])) ≤ 5 := by
    have := Submodule.finrank_le (primaryComponent (endP (P : GL (Fin 5) K)) (a : K[X]))
    rwa [Module.finrank_fin_fun] at this
  have h3 : (a : K[X]).natDegree = 5 := by rw [haeq, natDegree_X_pow_sub_C]
  rw [h1, h3] at h2
  change Module.finrank (AdjoinRoot (a : K[X])) (primaryComponent (endP (P : GL (Fin 5) K))
    (a : K[X])) ≤ 1
  omega

variable (h)

include h in
theorem primaryFactors_form (h5 : 5 ∣ 2 ^ f + 1) {P : unit5 h} {c : Kˣ}
    (hc : c ^ (2 ^ f + 1) = 1)
    (hP5 : (P : GL (Fin 5) K) ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin 5) c)
    (hb : ∃ b : K, b ^ 5 = c) (a : K[X]) (ha : a ∈ primaryFactors (endP (P : GL (Fin 5) K))) :
    ∃ μ : K, μ ≠ 0 ∧ μ ^ 5 = c ∧ h.bar μ * μ = 1 ∧ a = X - C μ := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_five h h5
  obtain ⟨b, hb⟩ := hb
  have hsplit : (X ^ 5 - C (c : K)).Splits := X_pow_sub_C_splits_of_isPrimitiveRoot hζ hb
  have hp0 : (X ^ 5 - C (c : K) : K[X]) ≠ 0 := X_pow_sub_C_ne_zero (by norm_num) _
  have hdvdp : minpoly K (endP (P : GL (Fin 5) K)) ∣ X ^ 5 - C (c : K) :=
    minpoly.dvd K _ (aeval_endP_eq_zero hP5)
  obtain ⟨hai, ham, hadvd⟩ := mem_primaryFactors.mp ha
  have hlin : a.natDegree = 1 :=
    (hsplit.of_dvd hp0 (hadvd.trans hdvdp)).natDegree_eq_one_of_irreducible hai
  have hform : a = X + C (a.coeff 0) := ham.eq_X_add_C hlin
  set μ : K := -(a.coeff 0) with hμ
  have haμ : a = X - C μ := by
    rw [hform, hμ, C_neg, sub_neg_eq_add]
  have hroot : (X ^ 5 - C (c : K) : K[X]).IsRoot μ := by
    have := (hadvd.trans hdvdp)
    rw [haμ, dvd_iff_isRoot] at this
    exact this
  have hμ5 : μ ^ 5 = c := by
    simpa [IsRoot, sub_eq_zero] using hroot
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0] at hμ5
    simp at hμ5
    exact c.ne_zero hμ5.symm
  exact ⟨μ, hμ0, hμ5, bar_mul_eq_one_of_pow_five h h5 hc hμ5, haμ⟩

end Five

section Main

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem two_le_two_pow_of_dvd (h5 : 5 ∣ 2 ^ f + 1) : 2 ≤ 2 ^ f := by
  have := four_le_two_pow h5
  omega

theorem su5_quasiFactored (h5 : 5 ∣ 2 ^ f + 1) {P : unit5 h} {c : Kˣ} (hc : c ^ (2 ^ f + 1) = 1)
    (hP5 : (P : GL (Fin 5) K) ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin 5) c)
    (hns : ∀ μ : Kˣ, (P : GL (Fin 5) K) ≠ Matrix.GeneralLinearGroup.scalar (Fin 5) μ) :
    QuasiFactored (cenSU h 5 (P : GL (Fin 5) K)) := by
  have hfin := h.finite
  have hq : 2 ≤ 2 ^ f := two_le_two_pow_of_dvd h5
  have HU := primaryData_toLin (h := h) P.2 Nat.prime_five (by norm_num) hP5
  by_cases hb : ∃ b : K, b ^ 5 = c
  · have hform : ∀ a : primaryFactors (endP (P : GL (Fin 5) K)), ∃ μ : K, μ ≠ 0 ∧ μ ^ 5 = c ∧
        h.bar μ * μ = 1 ∧ (a : K[X]) = X - C μ := fun a =>
      primaryFactors_form h h5 hc hP5 hb a a.2
    have hdeg : ∀ a : primaryFactors (endP (P : GL (Fin 5) K)), (a : K[X]).natDegree = 1 := by
      intro a
      obtain ⟨μ, -, -, -, ha⟩ := hform a
      rw [ha, natDegree_X_sub_C]
    have hself : ∀ a : primaryFactors (endP (P : GL (Fin 5) K)),
        dualPoly h.bar (a : K[X]) = a := by
      intro a
      obtain ⟨μ, hμ0, hμ5, hbm, ha⟩ := hform a
      have hbar0 : h.bar μ ≠ 0 := left_ne_zero_of_mul_eq_one hbm
      rw [ha, KCUnitaryBlock.dualPoly_X_sub_C hbar0, inv_eq_of_mul_eq_one_right hbm]
    have hmult4 : ∀ a : primaryFactors (endP (P : GL (Fin 5) K)),
        primaryMultiplicity (endP (P : GL (Fin 5) K)) (a : K[X]) ≤ 4 := by
      intro a
      by_contra hlt
      push Not at hlt
      obtain ⟨μ, hμ0, hμ5, hbm, ha⟩ := hform a
      have hm : primaryMultiplicity (endP (P : GL (Fin 5) K)) (a : K[X]) =
          Module.finrank K (primaryComponent (endP (P : GL (Fin 5) K)) (a : K[X])) := by
        rw [ha]
        exact KCUnitaryScalar.primaryMultiplicity_X_sub_C _ _
      have hle : Module.finrank K (primaryComponent (endP (P : GL (Fin 5) K)) (a : K[X])) ≤ 5 := by
        have := Submodule.finrank_le (primaryComponent (endP (P : GL (Fin 5) K)) (a : K[X]))
        rwa [Module.finrank_fin_fun] at this
      have htop : primaryComponent (endP (P : GL (Fin 5) K)) (a : K[X]) = ⊤ :=
        Submodule.eq_top_of_finrank_eq (by rw [Module.finrank_fin_fun]; omega)
      have hall : ∀ v : Fin 5 → K, (endP (P : GL (Fin 5) K)) v = μ • v := by
        intro v
        have hv : v ∈ primaryComponent (endP (P : GL (Fin 5) K)) (a : K[X]) := by
          rw [htop]; trivial
        rw [ha] at hv
        exact KCUnitaryScalar.mem_primaryComponent_X_sub_C.mp hv
      apply hns (Units.mk0 μ hμ0)
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.coe_scalar]
      apply Matrix.toLin'.injective
      refine LinearMap.ext fun v => ?_
      have h1 : ((P : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ v = μ • v := hall v
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply, h1]
      funext i
      simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
    have hexc : ∀ a : primaryFactors (endP (P : GL (Fin 5) K)),
        2 ≤ primaryMultiplicity (endP (P : GL (Fin 5) K)) (a : K[X]) →
        IsGoodBlock h (Matrix.GeneralLinearGroup.toLin (P : GL (Fin 5) K)) a := by
      intro a hm2
      refine ⟨hm2, fun _ hmem => ?_⟩
      rw [hdeg a, mul_one] at hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
      have := four_le_two_pow h5
      omega
    have hsd : ∀ a : primaryFactors (endP (P : GL (Fin 5) K)),
        IsGoodBlock h (Matrix.GeneralLinearGroup.toLin (P : GL (Fin 5) K)) a →
        dualPoly h.bar (a : K[X]) = a ∧
          Nat.Coprime (primaryMultiplicity (endP (P : GL (Fin 5) K)) (a : K[X]))
            ((2 ^ f) ^ (a : K[X]).natDegree + 1) := by
      intro a ha
      refine ⟨hself a, ?_⟩
      rw [hdeg a, pow_one]
      exact coprime_of_two_le_four h5 ha.1 (hmult4 a)
    exact cenSU_quasiFactored HU hq hexc (goodSplitAll_of_coprime HU hsd hq)
  · have hm := mult_le_one_of_no_root hP5 hb
    refine cenSU_quasiFactored HU hq (fun a h2 => ?_) (fun a ha => ?_)
    · exact absurd h2 (not_le.mpr (Nat.lt_of_le_of_lt (hm a) (by norm_num)))
    · exact absurd ha.1 (not_le.mpr (Nat.lt_of_le_of_lt (hm a) (by norm_num)))

theorem su5_comm_of_no_root (h5 : 5 ∣ 2 ^ f + 1) {P : unit5 h} {c : Kˣ}
    (hP5 : (P : GL (Fin 5) K) ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin 5) c)
    (hb : ¬ ∃ b : K, b ^ 5 = c) :
    ∀ a b : ↥(gramSU h (idGram K 5)), a ∈ cenSU h 5 (P : GL (Fin 5) K) →
      b ∈ cenSU h 5 (P : GL (Fin 5) K) → a * b = b * a := by
  have hfin := h.finite
  exact cenSU_comm_of_mult_le_one (primaryData_toLin (h := h) P.2 Nat.prime_five (by norm_num) hP5)
    (two_le_two_pow_of_dvd h5) (mult_le_one_of_no_root hP5 hb)

theorem su5_comm_of_shift (h5 : 5 ∣ 2 ^ f + 1) {P : unit5 h} {c : Kˣ} (hc : c ^ (2 ^ f + 1) = 1)
    (hP5 : (P : GL (Fin 5) K) ^ 5 = Matrix.GeneralLinearGroup.scalar (Fin 5) c)
    {g : ↥(gramSU h (idGram K 5))} {w : Kˣ} (hw5 : w ^ 5 = 1) (hw1 : w ≠ 1)
    (hg : (g : GL (Fin 5) K) * (P : GL (Fin 5) K) * (g : GL (Fin 5) K)⁻¹ =
      Matrix.GeneralLinearGroup.scalar (Fin 5) w * (P : GL (Fin 5) K)) :
    ∀ a b : ↥(gramSU h (idGram K 5)), a ∈ cenSU h 5 (P : GL (Fin 5) K) →
      b ∈ cenSU h 5 (P : GL (Fin 5) K) → a * b = b * a := by
  have hfin := h.finite
  by_cases hb : ∃ b : K, b ^ 5 = c
  · have HU := primaryData_toLin (h := h) P.2 Nat.prime_five (by norm_num) hP5
    refine cenSU_comm_of_mult_le_one HU (two_le_two_pow_of_dvd h5) ?_
    have hwK : IsPrimitiveRoot ((w : Kˣ) : K) 5 := by
      have hw : orderOf w = 5 := orderOf_eq_prime hw5 hw1
      have := IsPrimitiveRoot.orderOf w
      rw [hw] at this
      exact IsPrimitiveRoot.coe_units_iff.mpr this
    have hu : IsPrimitiveRoot (((w : Kˣ) : K))⁻¹ 5 := hwK.inv
    let G : (Fin 5 → K) ≃ₗ[K] (Fin 5 → K) :=
      LinearMap.GeneralLinearGroup.generalLinearEquiv K (Fin 5 → K)
        (Matrix.GeneralLinearGroup.toLin (g : GL (Fin 5) K))
    have hG : ∀ v, (endP (P : GL (Fin 5) K)) (G v) =
        (((w : Kˣ) : K))⁻¹ • G ((endP (P : GL (Fin 5) K)) v) := by
      intro v
      have h1 : (g : GL (Fin 5) K) * (P : GL (Fin 5) K) =
          Matrix.GeneralLinearGroup.scalar (Fin 5) w * ((P : GL (Fin 5) K) * (g : GL (Fin 5) K)) := by
        rw [← mul_assoc, ← hg]
        group
      have h2 : (P : GL (Fin 5) K) * (g : GL (Fin 5) K) =
          Matrix.GeneralLinearGroup.scalar (Fin 5) w⁻¹ * ((g : GL (Fin 5) K) * (P : GL (Fin 5) K)) := by
        rw [h1, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
      have h3 : ((P : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
          ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
          (((w : Kˣ) : K))⁻¹ • (((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
            ((P : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) := by
        have := congrArg (fun A : GL (Fin 5) K => (A : Matrix (Fin 5) (Fin 5) K)) h2
        simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar] at this
        rw [this, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, Units.val_inv_eq_inv_val]
      have e1 : G v = ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ v := rfl
      have e2 : (endP (P : GL (Fin 5) K)) v = ((P : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ v := rfl
      have e3 : (endP (P : GL (Fin 5) K)) (G v) = ((P : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ
          (((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ v) := rfl
      rw [e3, e2, Matrix.mulVec_mulVec]
      show _ = (((w : Kˣ) : K))⁻¹ • (((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ
        (((P : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ v))
      rw [Matrix.mulVec_mulVec, h3, Matrix.smul_mulVec]
    have hlin : ∀ a ∈ primaryFactors (endP (P : GL (Fin 5) K)), ∃ μ : K, μ ≠ 0 ∧ a = X - C μ := by
      intro a ha
      obtain ⟨μ, hμ0, -, -, haμ⟩ := primaryFactors_form h h5 hc hP5 hb a ha
      exact ⟨μ, hμ0, haμ⟩
    have hsq : Squarefree (minpoly K (endP (P : GL (Fin 5) K))) := HU.squarefree
    intro a
    exact mult_le_one_of_shift (Module.finrank_fin_fun K) hsq hlin hu G hG a a.2
  · exact su5_comm_of_no_root h5 hP5 hb

end Main

end CFSG.RankThree.PartOne.FOC
