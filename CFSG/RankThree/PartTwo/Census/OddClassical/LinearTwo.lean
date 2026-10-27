module

public import CFSG.RankThree.PartTwo.Census.Interface
public import CFSG.ClassicalInvolution.SL2Facts
import CFSG.RankThree.PartTwo.Census.Criteria
import CFSG.RankThree.PartTwo.Census.LinearRank
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.Adapters.LinearCatalog
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.ClassicalInvolution Matrix
open scoped MatrixGroups

variable {K : Type} [Field K]

local notation "M₂" => Matrix (Fin 2) (Fin 2) K

theorem pRank_three_PSL_two_le [Finite K] (hK3 : (3 : K) ≠ 0) (hodd : Odd (Nat.card K)) :
    Assembly.pRank 3 (⊤ : Subgroup PSL(2, K)) ≤ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : ¬ 3 ∣ Nat.card (Subgroup.center SL(2, K)) := by
    rw [sl2_natCard_center hodd]
    norm_num
  have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup PSL(2, K)) =
      CFSG.Open.pRank 3 (⊤ : Subgroup SL(2, K)) :=
    CFSG.SectionRank.pRank_quotient_eq _ hc
  have h2 := pRank_le_of_injective_GL (X := SL(2, K)) Nat.prime_three (by exact_mod_cast hK3)
    Matrix.SpecialLinearGroup.toGL Matrix.SpecialLinearGroup.toGL_injective
  rw [Fintype.card_fin] at h2
  change CFSG.Open.pRank 3 (⊤ : Subgroup PSL(2, K)) ≤ 2
  rw [h1]
  exact h2

theorem mul_self_eq_trace_smul_sub_det (M : Matrix (Fin 2) (Fin 2) K) :
    M * M = M.trace • M - M.det • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, trace_fin_two, det_fin_two] <;> ring

theorem mul_add_mul_eq_trace_smul {X Y : Matrix (Fin 2) (Fin 2) K} (hX : X.trace = 0)
    (hY : Y.trace = 0) : X * Y + Y * X = (X * Y).trace • 1 := by
  rw [trace_fin_two] at hX hY
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Matrix.add_apply, Matrix.mul_apply,
      Fin.sum_univ_two, trace_fin_two, Matrix.smul_apply, Matrix.one_apply_eq,
      Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), smul_eq_mul, mul_one, mul_zero]
  · linear_combination Y 0 0 * hX - X 1 1 * hY
  · linear_combination Y 0 1 * hX + X 0 1 * hY
  · linear_combination Y 1 0 * hX + X 1 0 * hY
  · linear_combination X 1 1 * hY - Y 0 0 * hX

theorem mem_center_of_coe_eq_smul {A : SL(2, K)} {c : K}
    (h : (A : Matrix (Fin 2) (Fin 2) K) = c • 1) : A ∈ Subgroup.center SL(2, K) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨c, ?_, ?_⟩
  · have hdet := A.2
    rw [h, det_smul, det_one, mul_one, Fintype.card_fin] at hdet
    exact hdet
  · rw [h, smul_one_eq_diagonal]
    rfl

theorem false_of_char_three [CharP K 3] {A B : SL(2, K)}
    (hA3 : A ^ 3 ∈ Subgroup.center SL(2, K)) (hA : A ∉ Subgroup.center SL(2, K))
    (hB2 : B ^ 2 ∈ Subgroup.center SL(2, K)) (hB : B ∉ Subgroup.center SL(2, K))
    (hAB : A * B * A⁻¹ * B⁻¹ ∈ Subgroup.center SL(2, K)) : False := by
  have h2 : (2 : K) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff K 3 2).mp (by exact_mod_cast h0)
    omega
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  have hneg : (-1 : SL(2, K)) ∈ Subgroup.center SL(2, K) := (mem_center_sl2_iff _).mpr (Or.inr rfl)
  have hBB : (B : Matrix (Fin 2) (Fin 2) K) * B = -1 := by
    rcases (mem_center_sl2_iff _).mp hB2 with h | h
    · exfalso
      apply hB
      have hinv : B⁻¹ = B := by
        rw [inv_eq_iff_mul_eq_one, ← pow_two, h]
      rcases CFSG.Semidihedral.OddFieldSL2.eq_one_or_minusIdentity_of_inv_eq_self K h2 B hinv with
        h' | h'
      · rw [h']
        exact Subgroup.one_mem _
      · rw [h']
        exact hneg
    · have := congrArg Subtype.val (show B * B = -1 by rw [← pow_two]; exact h)
      change (B : M₂) * B = ((-1 : SL(2, K)) : M₂) at this
      rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one] at this
      exact this
  have hBdet : (B : Matrix (Fin 2) (Fin 2) K).det = 1 := B.2
  have htrB : (B : Matrix (Fin 2) (Fin 2) K).trace = 0 := by
    have hch := mul_self_eq_trace_smul_sub_det (B : Matrix (Fin 2) (Fin 2) K)
    rw [hBB, hBdet, one_smul, eq_sub_iff_add_eq, neg_add_cancel] at hch
    rcases smul_eq_zero.mp hch.symm with h | h
    · exact h
    · exfalso
      rw [h, Matrix.det_zero] at hBdet
      exact zero_ne_one hBdet
  obtain ⟨A', hA'3, hA', hA'B⟩ : ∃ A' : SL(2, K), A' ^ 3 = 1 ∧ A' ∉ Subgroup.center SL(2, K) ∧
      (A' * B * A'⁻¹ * B⁻¹ ∈ Subgroup.center SL(2, K)) := by
    rcases (mem_center_sl2_iff _).mp hA3 with h | h
    · exact ⟨A, h, hA, hAB⟩
    · refine ⟨-A, ?_, fun hc => hA ?_, ?_⟩
      · rw [Odd.neg_pow (by decide), h, neg_neg]
      · have : -1 * (-A) ∈ Subgroup.center SL(2, K) := Subgroup.mul_mem _ hneg hc
        rwa [neg_one_mul, neg_neg] at this
      · have hinv : (-A)⁻¹ = -A⁻¹ :=
          inv_eq_of_mul_eq_one_right (by rw [neg_mul_neg, mul_inv_cancel])
        rwa [hinv, neg_mul, neg_mul_neg]
  have hA'det : (A' : M₂).det = 1 := A'.2
  have hch := mul_self_eq_trace_smul_sub_det (A' : M₂)
  rw [hA'det, one_smul] at hch
  set τ := (A' : M₂).trace with hτdef
  have hcube : (A' : M₂) * A' * A' = 1 := by
    have := congrArg Subtype.val (show A' * A' * A' = 1 by rw [← pow_three']; exact hA'3)
    exact this
  have hcube' : (τ ^ 2 - 1) • (A' : M₂) = (τ + 1) • (1 : M₂) := by
    rw [hch, sub_mul, smul_mul_assoc, hch, Matrix.one_mul] at hcube
    linear_combination (norm := module) hcube
  have hτ : τ = -1 := by
    by_cases hτ2 : τ ^ 2 - 1 = 0
    · have : (τ - 1) * (τ + 1) = 0 := by linear_combination hτ2
      rcases mul_eq_zero.mp this with h | h
      · exfalso
        have hτ1 : τ = 1 := sub_eq_zero.mp h
        rw [hτ1] at hcube'
        have := congrArg (fun X : M₂ => X 0 0) hcube'
        simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at this
        apply h2
        linear_combination -this
      · linear_combination h
    · exfalso
      apply hA'
      refine mem_center_of_coe_eq_smul (c := (τ ^ 2 - 1)⁻¹ * (τ + 1)) ?_
      rw [mul_smul, ← hcube', smul_smul, inv_mul_cancel₀ hτ2, one_smul]
  set N : M₂ := (A' : M₂) - 1 with hN
  have hNtr : N.trace = 0 := by
    rw [hN, trace_sub, trace_one, Fintype.card_fin, ← hτdef, hτ]
    push_cast
    linear_combination -h3
  have hNN : N * N = 0 := by
    have h3A : (3 : K) • (A' : M₂) = 0 := by rw [h3, zero_smul]
    rw [hN, sub_mul, mul_sub, mul_sub, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one, hch, hτ]
    linear_combination (norm := module) -h3A
  have hN0 : N ≠ 0 := by
    intro h0
    apply hA'
    refine mem_center_of_coe_eq_smul (c := 1) ?_
    rw [one_smul, ← sub_eq_zero]
    exact h0
  have hpol := mul_add_mul_eq_trace_smul hNtr htrB
  rcases (mem_center_sl2_iff _).mp hA'B with h | h
  ·
    have h' : A' * B = B * A' := mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h)
    have hcomm : (A' : M₂) * B = B * A' := congrArg Subtype.val h'
    have hNB : N * B = B * N := by
      rw [hN, sub_mul, mul_sub, hcomm, Matrix.one_mul, Matrix.mul_one]
    rw [← hNB] at hpol
    have hs : N * B = ((2 : K)⁻¹ * (N * B).trace) • (1 : M₂) := by
      rw [mul_smul, ← hpol, ← two_smul K (N * B), smul_smul, inv_mul_cancel₀ h2, one_smul]
    have hsq : (N * B) * (N * B) = 0 := by
      have e : (N * B) * (N * B) = (N * N) * (B * B) := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (B : M₂) N, ← hNB, Matrix.mul_assoc,
          Matrix.mul_assoc]
      rw [e, hNN, Matrix.zero_mul]
    rw [hs, smul_mul_smul_comm, Matrix.one_mul, smul_eq_zero] at hsq
    rcases hsq with hs0 | hs0
    · rw [mul_self_eq_zero] at hs0
      rw [hs0, zero_smul] at hs
      apply hN0
      calc N = -(N * ((B : M₂) * B)) := by rw [hBB, mul_neg, Matrix.mul_one, neg_neg]
        _ = -(N * B * B) := by rw [Matrix.mul_assoc]
        _ = 0 := by rw [hs, Matrix.zero_mul, neg_zero]
    · exact one_ne_zero hs0
  ·
    have h' : A' * B = -1 * B * A' :=
      mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_iff_eq_mul.mp h)
    have hanti : (A' : M₂) * B = -((B : M₂) * A') := by
      have := congrArg Subtype.val h'
      change (A' : M₂) * B = ((-1 : SL(2, K)) : M₂) * B * A' at this
      rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one, neg_one_mul,
        neg_mul] at this
      exact this
    have hNB : N * B + B * N = (-2 : K) • (B : M₂) := by
      rw [hN, sub_mul, mul_sub, hanti, Matrix.one_mul, Matrix.mul_one,
        show (-2 : K) • (B : M₂) = -(B : M₂) - B by
          rw [show (-2 : K) = -1 - 1 by norm_num, sub_smul, neg_one_smul, one_smul]]
      abel
    rw [hNB] at hpol
    apply hB
    refine mem_center_of_coe_eq_smul (c := (-2 : K)⁻¹ * (N * B).trace) ?_
    rw [mul_smul, ← hpol, smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr h2), one_smul]

theorem not_commute_PSL_two_char_three [CharP K 3] (a t : PSL(2, K)) (ha : orderOf a = 3)
    (ht : orderOf t = 2) : a * t ≠ t * a := by
  intro hat
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨B, rfl⟩ := QuotientGroup.mk_surjective t
  have hmem : ∀ X : SL(2, K), (QuotientGroup.mk X : PSL(2, K)) = 1 →
      X ∈ Subgroup.center SL(2, K) := fun X hX => (QuotientGroup.eq_one_iff X).mp hX
  have hnmem : ∀ X : SL(2, K), (QuotientGroup.mk X : PSL(2, K)) ≠ 1 →
      X ∉ Subgroup.center SL(2, K) := fun X hX hc => hX ((QuotientGroup.eq_one_iff X).mpr hc)
  refine false_of_char_three (A := A) (B := B) (hmem _ ?_) (hnmem _ ?_) (hmem _ ?_)
    (hnmem _ ?_) (hmem _ ?_)
  · have := pow_orderOf_eq_one (QuotientGroup.mk A : PSL(2, K))
    rw [ha] at this
    rw [QuotientGroup.mk_pow]
    exact this
  · intro h1
    rw [h1, orderOf_one] at ha
    omega
  · have := pow_orderOf_eq_one (QuotientGroup.mk B : PSL(2, K))
    rw [ht] at this
    rw [QuotientGroup.mk_pow]
    exact this
  · intro h1
    rw [h1, orderOf_one] at ht
    omega
  · rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, hat]
    group

theorem excluded433_A_one_odd (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.A 1 q).Valid)
    (hq : q.p ≠ 2) : Excluded433 (.lie ⟨.A 1 q, hv⟩) := by
  intro G _ _ hG e
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hf : q.exponent ≠ 0 := q.exponent_pos.ne'
  set K := GaloisField q.p q.exponent
  have e' := e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv)
  refine hG.false_of_localRank_three_le_two e' ?_
  by_cases h3 : q.p = 3
  · have : CharP K 3 := h3 ▸ (inferInstance : CharP K q.p)
    exact (localRank_three_le_one_of_forall_ne (not_commute_PSL_two_char_three)).trans
      (by norm_num)
  · refine localRank_le_of_pRank_le Nat.prime_three (pRank_three_PSL_two_le ?_ ?_)
    · intro h0
      have := (CharP.cast_eq_zero_iff K q.p 3).mp (by exact_mod_cast h0)
      exact h3 ((Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).mp this)
    · rw [GaloisField.card q.p q.exponent hf]
      exact (Nat.Prime.odd_of_ne_two q.prime_p hq).pow

end CFSG.RankThree.PartTwo.Census
