module

import CFSG.GroupTheory.InnerCentralizerProjection
import CFSG.RankThree.PartTwo.KFacts.AutTrialityComm
public import CFSG.RankThree.PartTwo.Sec4.Statements
import CFSG.RankThree.PartTwo.Sec14.Item148Res4ProofImgLe
import CFSG.RankThree.PartTwo.Sec16.Item166Res4ProofOrders

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof167Empty

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.KFacts
open scoped commutatorElement

theorem le_sup_centralizer_of_le_commutator_of_isoLThreePi {Γ : Type} [Group Γ] [Finite Γ]
    {X R T : Subgroup Γ} {m : ℕ} (hm : 2 ≤ m) (hX : Sec4.IsoLThreePi ↥X 2 m)
    (hRX : R ≤ Subgroup.normalizer (X : Set Γ)) (hTX : T ≤ Subgroup.normalizer (X : Set Γ))
    (hRT : R ≤ ⁅R, T⁆) (hR : Nat.Coprime 3 (Nat.card R)) :
    R ≤ X ⊔ Subgroup.centralizer (X : Set Γ) := by
  refine le_sup_centralizer_of_forall_mem_range_conj hRX ?_
  intro r hr
  have hσmem : X.normalizerMonoidHom ⟨r, hRX hr⟩ ∈ commutator (MulAut ↥X) :=
    normalizerMonoidHom_mem_commutator hRX hTX hRT hr
  have hcop : Nat.Coprime 3 (orderOf (X.normalizerMonoidHom ⟨r, hRX hr⟩)) := by
    refine Nat.Coprime.coprime_dvd_right ?_ hR
    refine (orderOf_map_dvd X.normalizerMonoidHom ⟨r, hRX hr⟩).trans ?_
    rw [← Subgroup.orderOf_coe]
    exact Subgroup.orderOf_dvd_natCard R hr
  exact Sec14.Item148Res4.isInnerAut_of_mem_commutator_of_coprime hm hX hσmem hcop

section TrialityCertificates


theorem le_sup_centralizer_of_le_commutator_of_trialityD4 {Γ : Type} [Group Γ]
    [Finite Γ] {X R T : Subgroup Γ} {n : ℕ}
    (hX : CFSG.Blueprint.ChevalleyExceptionalModel ↥X .trialityD4 2 n)
    (hRX : R ≤ Subgroup.normalizer (X : Set Γ)) (hTX : T ≤ Subgroup.normalizer (X : Set Γ))
    (hRT : R ≤ ⁅R, T⁆) : R ≤ X ⊔ Subgroup.centralizer (X : Set Γ) := by
  refine le_sup_centralizer_of_forall_mem_range_conj hRX ?_
  intro r hr
  have hσmem : X.normalizerMonoidHom ⟨r, hRX hr⟩ ∈ commutator (MulAut ↥X) :=
    normalizerMonoidHom_mem_commutator hRX hTX hRT hr
  exact isInnerAut_of_mem_commutator_of_trialityD4 hX hσmem

end TrialityCertificates

private theorem odd_two_pow_sq_sub_one {a : ℕ} (ha : 1 ≤ a) : Odd ((2 ^ a) ^ 2 - 1) := by
  have he : Even ((2 ^ a) ^ 2) := by
    rw [← pow_mul]
    exact Nat.even_pow.mpr ⟨even_two, by positivity⟩
  exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by positivity)) he odd_one

private theorem odd_two_pow_cube_sub_one {a : ℕ} (ha : 1 ≤ a) : Odd ((2 ^ a) ^ 3 - 1) := by
  have he : Even ((2 ^ a) ^ 3) := by
    rw [← pow_mul]
    exact Nat.even_pow.mpr ⟨even_two, by positivity⟩
  exact Nat.Even.sub_odd (Nat.one_le_pow _ _ (by positivity)) he odd_one

private theorem odd_two_pow_cube_add_one {a : ℕ} (ha : 1 ≤ a) : Odd ((2 ^ a) ^ 3 + 1) := by
  have he : Even ((2 ^ a) ^ 3) := by
    rw [← pow_mul]
    exact Nat.even_pow.mpr ⟨even_two, by positivity⟩
  exact he.add_one

private theorem three_mul_card_eq_two_pow_mul_odd {X : Type} [Group X] {a : ℕ} (ha : 1 ≤ a)
    (hX : Sec4.IsoLThreePi X 2 a) :
    ∃ s : ℕ, Odd s ∧ 3 * Nat.card X = 2 ^ (3 * a) * s := by
  have hpow : (2 ^ a) ^ 3 = 2 ^ (3 * a) := by rw [← pow_mul, mul_comm]
  rcases Proof166Res4.three_mul_card_of_isoLThreePi ha hX with h | h
  · refine ⟨((2 ^ a) ^ 2 - 1) * ((2 ^ a) ^ 3 - 1), ?_, ?_⟩
    · exact (odd_two_pow_sq_sub_one ha).mul (odd_two_pow_cube_sub_one ha)
    · rw [h, hpow]
  · refine ⟨((2 ^ a) ^ 2 - 1) * ((2 ^ a) ^ 3 + 1), ?_, ?_⟩
    · exact (odd_two_pow_sq_sub_one ha).mul (odd_two_pow_cube_add_one ha)
    · rw [h, hpow]

theorem eq_of_isoLThreePi_two {X : Type} [Group X] [Finite X] {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hXa : Sec4.IsoLThreePi X 2 a) (hXb : Sec4.IsoLThreePi X 2 b) : a = b := by
  obtain ⟨ra, hra, heqa⟩ := three_mul_card_eq_two_pow_mul_odd ha hXa
  obtain ⟨rb, hrb, heqb⟩ := three_mul_card_eq_two_pow_mul_odd hb hXb
  have heq : 2 ^ (3 * a) * ra = 2 ^ (3 * b) * rb := by
    rw [← heqa, ← heqb]
  have h3 : 3 * a = 3 * b := Sec14.Item148Rank.eq_of_two_pow_mul_odd148 hra hrb heq
  omega

end CFSG.RankThree.PartTwo.Sec16.Proof167Empty

end
