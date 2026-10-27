module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res6ProofTauMain
public import CFSG.RankThree.PartTwo.Sec21.Item211Res6ProofLinInner

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item211Res6Proof

open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.ComponentClassification
open CFSG.Assembly (IsElemAbelian)
open Item211Lie2Proof Item211Res5Proof
open scoped MatrixGroups Matrix

section Triv

variable {K : Type} [Field K]

theorem outerCentConcl_of_fix_conj [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp3 : 3 < p)
    {T : Subgroup (MulAut (projectiveSL 3 K))} (g : GL (Fin 3) K)
    (hfix : ∀ t ∈ T, t (conjAut 3 K g (proj 3 K tauOne)) = conjAut 3 K g (proj 3 K tauOne) ∧
      t (conjAut 3 K g (proj 3 K tauTwo)) = conjAut 3 K g (proj 3 K tauTwo)) :
    OuterCentConcl (innP K) T := by
  set a := conjAut 3 K g with ha
  refine outerCentConcl_of_conj a⁻¹ (outerCentConcl_of_tau hp3 ?_ ?_)
  · rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    refine mul_conj_eq_of_apply ?_
    change (a⁻¹ * t * a⁻¹⁻¹) (proj 3 K tauOne) = proj 3 K tauOne
    rw [inv_inv, MulAut.mul_apply, MulAut.mul_apply, (hfix t ht).1, MulAut.inv_apply,
      MulEquiv.symm_apply_apply]
  · rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    refine mul_conj_eq_of_apply ?_
    change (a⁻¹ * t * a⁻¹⁻¹) (proj 3 K tauTwo) = proj 3 K tauTwo
    rw [inv_inv, MulAut.mul_apply, MulAut.mul_apply, (hfix t ht).2, MulAut.inv_apply,
      MulEquiv.symm_apply_apply]

theorem fieldAut_proj_tauOne (σ : K ≃+* K) :
    fieldAut 3 K σ (proj 3 K tauOne) = proj 3 K tauOne := by
  rw [fieldAut_proj]
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  change (mOne : Matrix (Fin 3) (Fin 3) K).map σ = mOne
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mOne, map_ofNat]

theorem fieldAut_proj_tauTwo (σ : K ≃+* K) :
    fieldAut 3 K σ (proj 3 K tauTwo) = proj 3 K tauTwo := by
  rw [fieldAut_proj]
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  change (mTwo : Matrix (Fin 3) (Fin 3) K).map σ = mTwo
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mTwo, map_ofNat]

theorem eq_one_of_mem_linearAutGroup [Finite K] {T : Subgroup (MulAut (projectiveSL 3 K))}
    (hT2 : IsPGroup 2 T) (hR : T ⊓ innP K = ⊥) {t : MulAut (projectiveSL 3 K)} (ht : t ∈ T)
    {A : GL (Fin 3) K} (htA : t = conjAut 3 K A) : t = 1 := by
  obtain ⟨e, he⟩ := hT2 ⟨t, ht⟩
  have he' : t ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
  have h3 : ¬ 3 ∣ 2 ^ e := fun h => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h)
    omega
  rw [htA] at he'
  have hI := conjAut_mem_range_of_pow_eq_one he' h3
  rw [← htA] at hI
  have : t ∈ T ⊓ innP K := ⟨ht, hI⟩
  rw [hR, Subgroup.mem_bot] at this
  exact this

theorem outerCentConcl_of_semilinear [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp3 : 3 < p)
    {T : Subgroup (MulAut (projectiveSL 3 K))} (hT2 : IsPGroup 2 T) (hR : T ⊓ innP K = ⊥)
    (hsemi : ∀ t ∈ T, t ∈ semilinearAutGroup 3 K) : OuterCentConcl (innP K) T := by
  classical
  set φ := ProjectivePlane.linearFieldPart K (le_refl 3) with hφ
  have hker : ∀ t ∈ T, φ t = 1 → t = 1 := by
    intro t ht h1
    obtain ⟨A, σ, rfl⟩ := mem_semilinearAutGroup_iff.mp (hsemi t ht)
    have hσ : σ = 1 := by
      have := ProjectivePlane.linearFieldPart_eq (K := K) (le_refl 3) (A := A) (σ := σ)
        (Nat.zero_le 1)
      rw [pow_zero, mul_one] at this
      rw [← this]
      exact h1
    subst hσ
    exact eq_one_of_mem_linearAutGroup hT2 hR ht (by rw [map_one, mul_one])
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hf⟩ := FiniteField.card K p
  have hcyc : IsCyclic (K ≃+* K) := (card_ringAut_and_isCyclic (Fact.out : p.Prime) K
    (by rw [Nat.card_eq_fintype_card, hf.2])).2
  obtain ⟨⟨σ₁, hσ₁⟩, hgen⟩ := IsCyclic.exists_generator (α := T.map φ)
  obtain ⟨t₁, ht₁, rfl⟩ := hσ₁
  have hpow : ∀ t ∈ T, ∃ k : ℤ, t = t₁ ^ k := by
    intro t ht
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨φ t, ⟨t, ht, rfl⟩⟩)
    refine ⟨k, ?_⟩
    have h1 : φ t₁ ^ k = φ t := by simpa using congrArg Subtype.val hk
    have h2 := hker _ (T.mul_mem (T.inv_mem (T.zpow_mem ht₁ k)) ht)
      (by rw [map_mul, map_inv, map_zpow, h1, inv_mul_cancel])
    calc t = t₁ ^ k * ((t₁ ^ k)⁻¹ * t) := by group
      _ = t₁ ^ k := by rw [h2, mul_one]
  obtain ⟨A, σ, ht₁eq⟩ := mem_semilinearAutGroup_iff.mp (hsemi t₁ ht₁)
  have hφt₁ : φ t₁ = σ := by
    rw [ht₁eq]
    have := ProjectivePlane.linearFieldPart_eq (K := K) (le_refl 3) (A := A) (σ := σ)
      (Nat.zero_le 1)
    rwa [pow_zero, mul_one] at this
  have : Finite (K ≃+* K) := CFSG.GH74.GLS.IVK.instFiniteRingEquiv K
  set h := orderOf σ with hh
  have hσh : σ ^ h = 1 := pow_orderOf_eq_one σ
  have ht₁h : t₁ ^ h = 1 := hker _ (T.pow_mem ht₁ h) (by rw [map_pow, hφt₁, hσh])
  rw [ht₁eq, ProjectivePlane.conjAut_mul_fieldAut_pow, hσh, map_one, mul_one] at ht₁h
  obtain ⟨c, hc⟩ := exists_scalar_of_conjAut_eq (ht₁h.trans (map_one _).symm)
  rw [mul_one] at hc
  obtain ⟨H, d, hHd⟩ := CFSG.StandardType.OrdPRest.exists_hilbert90 (n := 3) (by norm_num) rfl A
    hc
  have ht₁H := CFSG.StandardType.OrdPRest.conjAut_mul_fieldAut_eq_conj' A H σ d hHd
  refine outerCentConcl_of_fix_conj hp3 H fun t ht => ?_
  obtain ⟨k, rfl⟩ := hpow t ht
  rw [ht₁eq, ht₁H]
  have hconj : (conjAut 3 K H * fieldAut 3 K σ * (conjAut 3 K H)⁻¹) ^ k =
      conjAut 3 K H * fieldAut 3 K (σ ^ k) * (conjAut 3 K H)⁻¹ := by
    rw [conj_zpow, map_zpow]
  rw [hconj]
  constructor
  · rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply,
      fieldAut_proj_tauOne]
  · rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply,
      fieldAut_proj_tauTwo]

end Triv

end Item211Res6Proof

end CFSG.RankThree.PartTwo.Sec21
