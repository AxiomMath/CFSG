module

public import CFSG.Mathlib.Arithmetic.TwoPowModThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour
public import CFSG.Adapters.QiuzhenLegacy.Glauberman.RelIndexSup
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Basic
public import CFSG.Quasithin.H13.L32NSp4Over
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQS

open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19 (IsZModSq)
open scoped Pointwise

theorem subset_pCore_mul_of_not_three_dvd_relIndex {X : Type} [Group X] [Finite X]
    {I A J : Subgroup X} (hAI : A ≤ I) (hJI : J ≤ I)
    (hAJ : A ≤ Subgroup.normalizer (J : Set X)) (hgroup : IsPGroup 3 (Bar2 J))
    (h3 : ¬ 3 ∣ A.relIndex I) :
    (J : Set X) ⊆ (CFSG.Open.pCoreOf 2 J : Set X) * (A : Set X) := by
  have hAJi : ¬ 3 ∣ (A ⊓ J).relIndex J := by
    rw [← (CFSG.GroupTheory.relIndex_sup_eq_relIndex_inf_of_le_normalizer hAJ).1]
    intro h
    apply h3
    rw [← Subgroup.relIndex_mul_relIndex (H := A) (K := A ⊔ J) (L := I) le_sup_left
      (sup_le hAI hJI)]
    exact h.mul_right _
  have : Finite (Bar2 J) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥J))
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hgroup.exists_card_eq
  set P := CFSG.Open.pCoreOf 2 J with hPdef
  have hP : P.relIndex J = 3 ^ k := by
    rw [← hk, hPdef, Subgroup.relIndex, CFSG.openPCoreOf_subgroupOf, Subgroup.index_eq_card]
  have h1 : (P ⊔ (A ⊓ J)).relIndex J ∣ 3 ^ k :=
    hP ▸ Subgroup.relIndex_dvd_of_le_left J le_sup_left
  have h2 : (P ⊔ (A ⊓ J)).relIndex J ∣ (A ⊓ J).relIndex J :=
    Subgroup.relIndex_dvd_of_le_left J le_sup_right
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h1
  have hJle : J ≤ P ⊔ (A ⊓ J) := by
    rw [← Subgroup.relIndex_eq_one, hi]
    cases i with
    | zero => rfl
    | succ i => exact absurd ((dvd_pow_self 3 i.succ_ne_zero).trans (hi ▸ h2)) hAJi
  have hcoe : ((P ⊔ (A ⊓ J) : Subgroup X) : Set X) =
      (P : Set X) * ((A ⊓ J : Subgroup X) : Set X) :=
    Subgroup.coe_mul_of_right_le_normalizer_left P (A ⊓ J)
      (inf_le_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J))
  intro j hj
  have hj' : j ∈ ((P ⊔ (A ⊓ J) : Subgroup X) : Set X) := hJle hj
  rw [hcoe] at hj'
  obtain ⟨p, hp, y, hy, rfl⟩ := hj'
  exact Set.mul_mem_mul hp (Subgroup.mem_inf.mp hy).1

private theorem not_three_dvd_of_mod_three {k a : ℕ} (hk : (k + 1) % 3 = 1) :
    ¬ 3 ∣ (k + 1) ^ 4 * ((k + 2) * ((k + 2) * ((k + 1) ^ 3 + 1))) * 2 ^ a := by
  have hcop : ∀ m : ℕ, m % 3 ≠ 0 → Nat.Coprime 3 m := fun m hm =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (fun h => hm (Nat.mod_eq_zero_of_dvd h))
  have hcube : (k + 1) ^ 3 % 3 = 1 := by rw [Nat.pow_mod, hk]
  have c1 : Nat.Coprime 3 (k + 1) := hcop _ (by omega)
  have c2 : Nat.Coprime 3 (k + 2) := hcop _ (by omega)
  have c3 : Nat.Coprime 3 ((k + 1) ^ 3 + 1) := hcop _ (by omega)
  have c4 : Nat.Coprime 3 (2 ^ a) := Nat.Coprime.pow_right a (by norm_num)
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
    (((c1.pow_right 4).mul_right (c2.mul_right (c2.mul_right c3))).mul_right c4)

theorem not_three_dvd_relIndex_of_l2u3 {X : Type} [Group X] [Finite X] {I A : Subgroup X}
    {n : ℕ} (hn : 2 ≤ n) (heven : Even n) (hI : S17.IsL2U3Product (Bar2 I) n) (hAI : A ≤ I)
    (hA : IsZModSq A n) : ¬ 3 ∣ A.relIndex I := by
  have : Finite (Bar2 I) :=
    Finite.of_surjective _ (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥I))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥I)).exists_card_eq
  have hm := CFSG.two_pow_mod_three_of_even heven
  have hgcd : Nat.gcd 3 (2 ^ n + 1) = 1 :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (by omega)
  have hbar := S17.card_mul_gcd_of_isL2U3Product_eq hI
  rw [hgcd, mul_one] at hbar
  have hIcard : Nat.card I = Nat.card (Bar2 I) * 2 ^ a := by
    rw [← ha]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hrel : A.relIndex I * Nat.card A = Nat.card I := by
    have h := Subgroup.relIndex_mul_card (H := A) (K := I)
    rwa [inf_eq_left.mpr hAI] at h
  rw [S19.card_eq_of_isZModSq hA, hIcard, hbar, pow_mul' 2 2 n, pow_mul' 2 3 n,
    pow_mul' 2 4 n] at hrel
  have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ n = k + 1 := ⟨2 ^ n - 1, by omega⟩
  have hsq : (k + 1) ^ 2 - 1 = k * (k + 2) := Nat.sub_eq_of_eq_add (by ring)
  rw [hk, Nat.add_sub_cancel, hsq] at hrel
  have hkpos : 0 < k * k := Nat.mul_pos (by omega) (by omega)
  have heq : A.relIndex I = (k + 1) ^ 4 * ((k + 2) * ((k + 2) * ((k + 1) ^ 3 + 1))) * 2 ^ a := by
    apply Nat.eq_of_mul_eq_mul_right hkpos
    rw [hrel]
    ring
  rw [heq]
  exact not_three_dvd_of_mod_three (by omega)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQS

end
