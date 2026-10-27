module

public import CFSG.RankThree.PartTwo.KFacts.K71Item93
public import CFSG.RankThree.PartTwo.KFacts.K71SU3Field
public import CFSG.RankThree.PartTwo.KFacts.K71SU3Torus

public noncomputable section

namespace CFSG.RankThree.PartTwo.KFacts

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open Matrix

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem mulAut_conj_eq_suConj {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)
    (x : unitarySU p f K 3) :
    MulAut.conj x = suConj h ⟨x, unitarySU_le_unitaryIsom3 x.2⟩ := by
  refine MulEquiv.ext fun g => Subtype.ext ?_
  rw [MulAut.conj_apply, coe_suConj]
  rfl

theorem mulAut_pow_mod_three {M : Type*} [Monoid M] {φ : M} (hφ : φ ^ 3 = 1) (n : ℕ) :
    φ ^ n = φ ^ (n % 3) := by
  conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, hφ, one_pow, one_mul]

theorem eq_one_of_suConj_eq_suConj_mul_suField {p f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData p f K) (hq : 2 < p ^ f) {X Y : unitaryIsom3 h} {δ : K ≃+* K}
    (hXY : suConj h X = suConj h Y * suField h δ) : δ = 1 := by
  have h1 : suConj h (X⁻¹ * Y) * suField h δ = 1 := by
    rw [map_mul, mul_assoc, ← hXY, map_inv, inv_mul_cancel]
  have h2 := congrArg (suDescend h hq) h1
  rw [map_mul, suDescend_suConj, suDescend_suField, map_one] at h2
  exact (eq_one_of_psuConj_mul_psuField_eq_one _ _ h2).1

theorem exists_conj_eq_suConj_of_hyp92_one {A : Subgroup G} {c a : G} {R : Subgroup G}
    (hyp : Sec9.Hyp92 G A c L a R 1) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    {K : Type} [Field K] {h : UnitaryFieldData 2 3 K}
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* unitarySU 2 3 K 3) {σ : K ≃+* K} (hσ3 : orderOf σ = 3)
    {B : unitaryIsom3 h} (hBσ : suConj h B * suField h σ = suField h σ * suConj h B)
    (hB3 : suConj h B ^ 3 = 1) (hB1 : suConj h B ≠ 1)
    (hA : ∀ y (hy : y ∈ A), ∃ i j : ℕ,
      inducedAutHom L e ⟨y, hAL hy⟩ = suConj h B ^ i * suField h σ ^ j) :
    ∃ w : unitarySU 2 3 K 3, w ^ 3 = 1 ∧ suConj h B = MulAut.conj w := by
  have hq : 2 < 2 ^ 3 := by norm_num
  by_contra hcon
  rcases su38_dichotomy h hσ3 B hBσ hB3 hB1 with ⟨w, hw3, -, hBw⟩ | ⟨x, hx3, hxs, hσx, hBx⟩
  · exact hcon ⟨w, hw3, hBw⟩
  obtain ⟨d, hdA, hγd⟩ := exists_mem_inducedAutHom_eq_conj_of_fixed hyp hAL e hA hx3 hσx hBx
  obtain ⟨i, j, hij⟩ := hA d hdA
  have h1 : MulAut.conj x = suConj h B ^ i * suField h σ ^ j := hγd.symm.trans hij
  have hσj : σ ^ j = 1 := by
    refine eq_one_of_suConj_eq_suConj_mul_suField h hq (X := ⟨x, unitarySU_le_unitaryIsom3 x.2⟩)
      (Y := B ^ i) ?_
    rw [← mulAut_conj_eq_suConj, h1, map_pow, map_pow]
  rw [← map_pow (suField h), hσj, map_one, mul_one] at h1
  rw [mulAut_pow_mod_three hB3 i] at h1
  obtain ⟨r, hr⟩ : ∃ r, r = i % 3 := ⟨_, rfl⟩
  rw [← hr] at h1
  have hr3 : r < 3 := hr ▸ Nat.mod_lt _ (by norm_num)
  interval_cases r
  ·
    rw [pow_zero] at h1
    obtain ⟨c', -, hc'⟩ := exists_scalar_of_conj_eq_one h hq h1
    apply hxs (c' : K)
    rw [hc', GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
  · rw [pow_one] at h1
    exact hcon ⟨x, hx3, h1.symm⟩
  · refine hcon ⟨x ^ 2, by rw [← pow_mul, mul_comm, pow_mul, hx3, one_pow], ?_⟩
    rw [map_pow, h1, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hB3, one_mul, pow_one]

theorem eq_bot_of_hyp92_one {A : Subgroup G} {c a : G} {R : Subgroup G}
    (hyp : Sec9.Hyp92 G A c L a R 1) (hAL : A ≤ Subgroup.normalizer (L : Set G)) {e : G}
    (heA : e ∈ A) (hec : e ∉ Subgroup.zpowers c) (he : e ∈ Subgroup.normalizer (L : Set G))
    (N : Subgroup (MulAut (L ⧸ aschbacherSolvableCore 3 L)))
    (hNc : ∀ ν ∈ N, ν * thetaQuotMulAut L (compAction L ⟨e, he⟩) =
      thetaQuotMulAut L (compAction L ⟨e, he⟩) * ν)
    (hN3 : ¬ 3 ∣ Nat.card N)
    (hNn : ∀ ℓ : L ⧸ aschbacherSolvableCore 3 L,
      thetaQuotMulAut L (compAction L ⟨e, he⟩) ℓ = ℓ →
        ∀ ν ∈ N, MulAut.conj ℓ * ν * (MulAut.conj ℓ)⁻¹ ∈ N) :
    N = ⊥ := by
  have hq : 2 < 2 ^ 3 := by norm_num
  obtain ⟨K, _, h, e', σ, B, b, hbA, hσ3, hγb, hBσ, hB3, hB1, hA⟩ :=
    exists_su38_model_of_hyp92_one hyp hAL
  have := h.finite
  obtain ⟨w, hw3, hBw⟩ := exists_conj_eq_suConj_of_hyp92_one hyp hAL e' hσ3 hBσ hB3 hB1 hA
  obtain ⟨i, j, hij⟩ := hA e heA
  have hσ3' : σ ^ 3 = 1 := by rw [← hσ3]; exact pow_orderOf_eq_one σ
  have hσf3 : suField h σ ^ 3 = 1 := by rw [← map_pow, hσ3', map_one]
  have hw3' : MulAut.conj w ^ 3 = 1 := by rw [← map_pow, hw3, map_one]
  have hwσ : Commute (MulAut.conj w) (suField h σ) := by
    rw [← hBw]
    exact hBσ
  have hε : MulAut.congr e' (thetaQuotMulAut L (compAction L ⟨e, he⟩)) =
      MulAut.conj (w ^ (i % 3)) * suField h σ ^ (j % 3) := by
    rw [← inducedAutHom_apply, show (⟨e, he⟩ : Subgroup.normalizer (L : Set G)) = ⟨e, hAL heA⟩
      from rfl, hij, hBw, mulAut_pow_mod_three hw3' i, mulAut_pow_mod_three hσf3 j, map_pow]
  have hε1 : MulAut.conj (w ^ (i % 3)) * suField h σ ^ (j % 3) ≠ 1 := by
    intro h1
    apply hec
    refine mem_zpowers_of_thetaQuotMulAut_eq_one hyp.toHyp81 he heA ?_
    have h2 := hε.trans h1
    exact (MulAut.congr e').injective (h2.trans (map_one _).symm)
  refine eq_bot_of_congr e' (fun N₀ hc h3 hn => ?_) hNc hN3 hNn
  rw [hε] at hc hn
  have hmodj : j % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hmodi : i % 3 < 3 := Nat.mod_lt _ (by norm_num)
  by_cases hj0 : j % 3 = 0
  ·
    rw [hj0, pow_zero, mul_one] at hc hn hε1
    have hu3 : (w ^ (i % 3)) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hw3, one_pow]
    have hus : ∀ c' : K, ((w ^ (i % 3) : unitarySU 2 3 K 3) : GL (Fin 3) K) ≠
        c' • (1 : Matrix (Fin 3) (Fin 3) K) := by
      intro c' hc'
      apply hε1
      refine MulEquiv.ext fun g => ?_
      rw [MulAut.conj_apply, MulAut.one_apply]
      have hcomm : w ^ (i % 3) * g = g * w ^ (i % 3) := by
        apply Subtype.ext
        apply Units.ext
        simp only [Subgroup.coe_mul, Units.val_mul, hc', Matrix.smul_mul, Matrix.one_mul,
          Matrix.mul_smul, Matrix.mul_one]
      rw [hcomm, mul_inv_cancel_right]
    exact eq_bot_of_commute_conj h hu3 hus hc h3 hn
  ·
    set ε' := MulAut.conj (w ^ (i % 3)) * suField h σ ^ (j % 3) with hε'
    have hε'3 : ε' ^ 3 = 1 := by
      have hc' : Commute (MulAut.conj (w ^ (i % 3))) (suField h σ ^ (j % 3)) := by
        rw [map_pow]
        exact (hwσ.pow_left _).pow_right _
      have e1 : MulAut.conj (w ^ (i % 3)) ^ 3 = 1 := by
        rw [← map_pow, ← pow_mul, mul_comm (i % 3) 3, pow_mul, hw3, one_pow, map_one]
      have e2 : (suField h σ ^ (j % 3)) ^ 3 = 1 := by
        rw [← pow_mul, mul_comm (j % 3) 3, pow_mul, hσf3, one_pow]
      rw [hε', hc'.mul_pow, e1, e2, one_mul]
    have hD : suDescend h hq ε' ∉ (psuConj h).range := by
      rintro ⟨X, hX⟩
      apply hj0
      have h1 : suConj h X = suConj h ⟨_, unitarySU_le_unitaryIsom3 (w ^ (i % 3)).2⟩ *
          suField h (σ ^ (j % 3)) := by
        apply eq_of_suDescend_eq h hq
        rw [suDescend_suConj, hX, hε', map_mul, mulAut_conj_eq_suConj h, ← map_pow (suField h),
          map_mul]
      have h2 := eq_one_of_suConj_eq_suConj_mul_suField h hq h1
      have h3 := orderOf_dvd_of_pow_eq_one h2
      rw [hσ3] at h3
      have h4 : j % 3 < 3 := hmodj
      omega
    have hα3 : suDescend h hq ε' ^ 3 = 1 := by rw [← map_pow, hε'3, map_one]
    obtain ⟨σ', hσ'3, H', hαH⟩ := unitary_order_three_field_descent hq _ hα3 hD
    have hlift : ε' = suConj h H' * suField h σ' * (suConj h H')⁻¹ := by
      apply eq_of_suDescend_eq h hq
      rw [hαH, map_mul, map_mul, map_inv, suDescend_suConj, suDescend_suField]
    exact eq_bot_of_conj hlift (fun N₁ hc₁ h₁ hn₁ => eq_bot_of_commute_suField h hσ'3 hc₁ h₁ hn₁)
      hc h3 hn

end CFSG.RankThree.PartTwo.KFacts
