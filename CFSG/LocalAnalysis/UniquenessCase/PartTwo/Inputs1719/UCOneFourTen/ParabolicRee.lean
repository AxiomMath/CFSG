module

public import CFSG.Blueprint.Catalog
import CFSG.LocalAnalysis.GLTheoremA.CatA.HDesc2Ree
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.InputsL33b
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactFieldAutEvenProj
public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open Subgroup

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ComponentClassification
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.SeitzGeneration

private lemma reeTitsModel_of_lieModel_twistedF4' {J : Type} [Group J] {n : ℕ}
    (hm : CFSG.Blueprint.LieModel J .twistedF4 0 2 n) :
    CFSG.Blueprint.ReeTitsModel J .twistedF4 2 n := by
  rcases hm with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hR⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact hR
  · exact absurd ht (by decide)

private lemma odd_three_le_of_lieModel_twistedF4 {J : Type} [Group J] {n : ℕ}
    (hm : CFSG.Blueprint.LieModel J .twistedF4 0 2 n) : Odd n ∧ 3 ≤ n := by
  have hadm := (reeTitsModel_of_lieModel_twistedF4' hm).1
  simp only [CFSG.Open.StatedLieAdmissible] at hadm
  obtain ⟨-, -, -, -, hodd, h3⟩ := hadm
  exact ⟨hodd, h3⟩

private lemma five_mod_two_pow_odd (a : ℕ) :
    (2 ^ (2 * a + 1)) % 5 = 2 ∨ (2 ^ (2 * a + 1)) % 5 = 3 := by
  induction a with
  | zero => left; norm_num
  | succ a ih =>
    have h : 2 ^ (2 * (a + 1) + 1) = 4 * 2 ^ (2 * a + 1) := by ring
    rw [h, Nat.mul_mod]
    rcases ih with h2 | h3
    · rw [h2]; norm_num
    · rw [h3]; norm_num

private lemma five_not_dvd_of_odd (a : ℕ) :
    ¬ 5 ∣ 2 ^ (2 * a + 1) ∧ ¬ 5 ∣ 2 ^ (2 * a + 1) - 1 ∧
      ¬ 5 ∣ 2 ^ (2 * a + 1) + 1 := by
  have hq := five_mod_two_pow_odd a
  have hq1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  have hq2 : 2 ≤ 2 ^ (2 * a + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.dvd_iff_mod_eq_zero]
    omega
  · intro h
    obtain ⟨k, hk⟩ := h
    have hqeq : 2 ^ (2 * a + 1) = 1 + 5 * k := by omega
    rw [hqeq, Nat.add_mul_mod_self_left] at hq
    norm_num at hq
  · intro h
    obtain ⟨k, hk⟩ := h
    have hk1 : 1 ≤ k := by omega
    have hqeq : 2 ^ (2 * a + 1) = 4 + 5 * (k - 1) := by omega
    rw [hqeq, Nat.add_mul_mod_self_left] at hq
    norm_num at hq

private lemma padicValNat_le_of_dvd_five {a b : ℕ} (hab : a ∣ b) (hb : b ≠ 0) :
    padicValNat 5 a ≤ padicValNat 5 b := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact (padicValNat_dvd_iff_le hb).1 (pow_padicValNat_dvd.trans hab)

private lemma padicValNat_five_reeParabolic_zero {q : ℕ} (hq2 : 2 ≤ q)
    (h5q : ¬ 5 ∣ q) (h5qm1 : ¬ 5 ∣ q - 1) (h5qp1 : ¬ 5 ∣ q + 1) :
    padicValNat 5 (q ^ 12 * (q - 1) ^ 2 * (q + 1)) = 0 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hq0 : q ≠ 0 := by omega
  have hqm1 : q - 1 ≠ 0 := by omega
  have hqp1 : q + 1 ≠ 0 := by omega
  rw [padicValNat.mul (mul_ne_zero (pow_ne_zero 12 hq0) (pow_ne_zero 2 hqm1)) hqp1,
    padicValNat.mul (pow_ne_zero 12 hq0) (pow_ne_zero 2 hqm1),
    padicValNat.pow, padicValNat.pow,
    padicValNat.eq_zero_of_not_dvd h5q,
    padicValNat.eq_zero_of_not_dvd h5qm1,
    padicValNat.eq_zero_of_not_dvd h5qp1]

private lemma padicValNat_five_reeParabolic_one {q : ℕ} (hq2 : 2 ≤ q)
    (h5q : ¬ 5 ∣ q) (h5qm1 : ¬ 5 ∣ q - 1) :
    padicValNat 5 (q ^ 12 * (q - 1) ^ 2 * (q ^ 2 + 1)) =
      padicValNat 5 (q ^ 2 + 1) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hq0 : q ≠ 0 := by omega
  have hqm1 : q - 1 ≠ 0 := by omega
  rw [padicValNat.mul (mul_ne_zero (pow_ne_zero 12 hq0) (pow_ne_zero 2 hqm1)) (by positivity),
    padicValNat.mul (pow_ne_zero 12 hq0) (pow_ne_zero 2 hqm1),
    padicValNat.pow, padicValNat.pow,
    padicValNat.eq_zero_of_not_dvd h5q,
    padicValNat.eq_zero_of_not_dvd h5qm1]
  ring

section certificates


private lemma padicValNat_five_card_reeLocalParabolic_le
    {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (j : Fin F4.fixedOrbitCount) :
    padicValNat 5 (Nat.card (F4.reeLocalParabolic K a j)) ≤
      padicValNat 5 ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
  obtain ⟨h5q, h5qm1, h5qp1⟩ := five_not_dvd_of_odd a
  have hq2 : 2 ≤ 2 ^ (2 * a + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  fin_cases j
  · rw [CFSG.LocalAnalysis.GLTheoremA.HDesc.card_reeLocalParabolic_zero hK,
      padicValNat_five_reeParabolic_zero hq2 h5q h5qm1 h5qp1]
    exact Nat.zero_le _
  · rw [CFSG.LocalAnalysis.GLTheoremA.HDesc.card_reeLocalParabolic_one hK,
      padicValNat_five_reeParabolic_one hq2 h5q h5qm1]

private lemma padicValNat_five_card_normalizer_reeGamma_le
    {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    {R : Subgroup ↥(F4.reeGamma K a)} (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R) :
    padicValNat 5 (Nat.card (Subgroup.normalizer (R : Set ↥(F4.reeGamma K a)))) ≤
      padicValNat 5 ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
  have hfin : Finite (ModGL F4.tag K) := finite_modGL
  set E : Subgroup ↥(F4.reeGamma K a) :=
    Subgroup.normalizer (R : Set ↥(F4.reeGamma K a)) with hE
  set A : Subgroup (ModGL F4.tag K) := E.map (F4.reeGamma K a).subtype with hA
  set R' : Subgroup (ModGL F4.tag K) := R.map (F4.reeGamma K a).subtype with hR'
  have hAΓ : A ≤ F4.reeGamma K a := Subgroup.map_subtype_le _
  have hRΓ : R' ≤ F4.reeGamma K a := Subgroup.map_subtype_le _
  have hR0 : R' ≠ ⊥ := fun h =>
    hR ((Subgroup.map_eq_bot_iff_of_injective R (F4.reeGamma K a).subtype_injective).1 h)
  have hRp : IsPGroup 2 R' := hR2.map _
  have hAR : A ≤ Subgroup.normalizer (R' : Set (ModGL F4.tag K)) :=
    Subgroup.le_normalizer_map _
  obtain ⟨y, hy, j, hj⟩ := exists_conj_le_reeLocalParabolic hK hAΓ hRΓ hR0 hRp hAR
  have hdiv : Nat.card E ∣ Nat.card (F4.reeLocalParabolic K a j) := by
    have h1 := Subgroup.card_dvd_of_le hj
    rw [Subgroup.card_map_of_injective (MulAut.conj y).injective] at h1
    rwa [hA, Subgroup.card_map_of_injective (F4.reeGamma K a).subtype_injective] at h1
  exact (padicValNat_le_of_dvd_five hdiv Nat.card_pos.ne').trans
    (padicValNat_five_card_reeLocalParabolic_le hK j)

end certificates


theorem center_eq_bot_of_lieModel_twistedF4
    {K : Type} [Group K] [Finite K] (hK : CFSG.Open.IsQuasisimple K) {n : ℕ}
    (hm : CFSG.Blueprint.LieModel (K ⧸ center K) .twistedF4 0 2 n) : center K = ⊥ := by
  obtain ⟨hodd, h3⟩ := odd_three_le_of_lieModel_twistedF4 hm
  obtain ⟨m, rfl⟩ := hodd
  have hm1 : 1 ≤ m := by omega
  have hL : CFSG.IsQuasisimple K :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native K).mp
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open K).mpr hK)
  have hmult := CFSG.LieType.Steinberg.CentralExt.GriessExceptional.reeF4_hopfMultiplier
    (X := K ⧸ center K) hm1 hm
  have : Subsingleton (CFSG.Open.griessHopfMultiplier (K ⧸ center K)) := hmult.2
  have hcard1 : Nat.card (CFSG.Open.griessHopfMultiplier (K ⧸ center K)) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
  have hdvd := CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33.natCard_center_dvd hL
    (MulEquiv.refl (K ⧸ center K))
  rw [hcard1] at hdvd
  exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp hdvd)

theorem padicValNat_five_card_normalizer_le_of_twistedF4
    {J : Type} [Group J] [Finite J] {n : ℕ} (hm : CFSG.Blueprint.LieModel J .twistedF4 0 2 n)
    {R : Subgroup J} (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R) :
    padicValNat 5 (Nat.card (normalizer (R : Set J))) ≤ padicValNat 5 (2 ^ (2 * n) + 1) := by
  have hRmodel := reeTitsModel_of_lieModel_twistedF4' hm
  obtain ⟨-, -, -, -, -, -, hmain⟩ :=
    UnbalancedCatalog.large_Ree_model_field_outer_group_and_inner_involutions J 2 n hRmodel
  obtain ⟨-, a, hfa, F, hField, hFinite, hFcard, hwit⟩ := hRmodel
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype F := Fintype.ofFinite F
  have : CharP F F4.prime := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by rw [← Nat.card_eq_fintype_card, hFcard])
  obtain ⟨⟨e⟩, -⟩ := hmain a F hfa hFcard hwit
  have hK : Nat.card F = 2 ^ (2 * a + 1) := by rw [hFcard, hfa]
  have : Finite (ModGL F4.tag F) := finite_modGL
  have hmap : R.map e.toMonoidHom ≠ ⊥ := fun h =>
    hR ((Subgroup.map_eq_bot_iff_of_injective R e.injective).1 h)
  have hmap2 : IsPGroup 2 (R.map e.toMonoidHom) := hR2.map _
  have hdiv :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KFAE.card_normalizer_dvd_of_mulEquiv e R
  have hle := padicValNat_le_of_dvd_five hdiv Nat.card_pos.ne'
  have hbound := padicValNat_five_card_normalizer_reeGamma_le hK hmap hmap2
  have hpow : ((2 ^ (2 * a + 1)) ^ 2 + 1) = 2 ^ (2 * n) + 1 := by
    rw [hfa]
    congr 1
    rw [show 2 * (2 * a + 1) = (2 * a + 1) * 2 by ring, pow_mul]
  rw [hpow] at hbound
  exact hle.trans hbound

theorem sq_dvd_card_of_lieModel_twistedF4
    {J : Type} [Group J] {n : ℕ} (hm : CFSG.Blueprint.LieModel J .twistedF4 0 2 n) :
    (2 ^ (2 * n) + 1) ^ 2 ∣ Nat.card J := by
  have hR := reeTitsModel_of_lieModel_twistedF4' hm
  rw [CFSG.AGLEmbedding.card_of_reeTitsModel_twistedF4_exact hR]
  set q := 2 ^ n with hq
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  have hq2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ hq1
  have hq24 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right hq1 (by norm_num)
  have hq41 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ hq1
  have h1 : q ^ 6 + 1 = (q ^ 2 + 1) * (q ^ 4 - q ^ 2 + 1) := by
    zify [hq2, hq24]
    ring
  have h2 : q ^ 4 - 1 = (q ^ 2 + 1) * (q ^ 2 - 1) := by
    zify [hq2, hq41]
    ring
  have hdvd : (q ^ 2 + 1) ^ 2 ∣ (q ^ 6 + 1) * (q ^ 4 - 1) := by
    rw [h1, h2, pow_two]
    exact mul_dvd_mul (dvd_mul_right _ _) (dvd_mul_right _ _)
  have h2n : 2 ^ (2 * n) = q ^ 2 := by
    rw [show 2 * n = n * 2 by ring, pow_mul]
  rw [h2n]
  simp only [CFSG.Open.ordTwistedF4]
  rw [show q ^ 12 * (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 3 + 1) * (q - 1) =
    (q ^ 6 + 1) * (q ^ 4 - 1) * (q ^ 12 * (q ^ 3 + 1) * (q - 1)) by ring]
  exact hdvd.mul_right _

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410
