module

public import CFSG.RankThree.GF2n.Smith81.InspOrthModels
import CFSG.RankThree.GF2n.Smith81.OrthE2Natural
import CFSG.RankThree.GF2n.Stroth80.GriessOrthSmall
import CFSG.GH74.Generic.S1.SymSchur
import CFSG.LocalAnalysis.ComponentInitial.UnitaryModelOuterTwoPart

public section

namespace CFSG.RankThree.GF2n.Smith81.Insp

open CFSG CFSG.Blueprint CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n.Stroth80
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem ordTwistedD_eq_of_even {m q : ℕ} (hm : 1 ≤ m) (hq : Even q) :
    ordTwistedD m q = q ^ (m * (m - 1)) * (q ^ m + 1) *
      ∏ i ∈ Finset.Icc 1 (m - 1), (q ^ (2 * i) - 1) := by
  have hodd : Odd (q ^ m + 1) := ((Nat.even_pow' (by omega)).mpr hq).add_one
  rw [ordTwistedD, Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd), Nat.div_one]

theorem card_statedOmega_minus_eq_ordTwistedD {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    (hm : 2 ≤ m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card ↥(StatedOmega (StatedQuadMinus m K b c)) = ordTwistedD m (Nat.card K) := by
  have hev : Even (Nat.card K) := by
    have := Fintype.ofFinite K
    obtain ⟨n, -, h⟩ := FiniteField.card K 2
    rw [Nat.card_eq_fintype_card, h]
    exact (Nat.even_pow' n.ne_zero).mpr even_two
  have h := card_statedOmega_minus_eq_of_two_le (K := K) hm hirr
  rw [ordTwistedD_eq_of_even (by omega) hev]
  have h1 : ∀ i, 1 ≤ Nat.card K ^ (2 * i) := fun i => Nat.one_le_pow _ _ Nat.card_pos
  have hcast : ((Nat.card K ^ (m * (m - 1)) * (Nat.card K ^ m + 1) *
      ∏ i ∈ Finset.Icc 1 (m - 1), (Nat.card K ^ (2 * i) - 1) : ℕ) : ℤ) =
      (Nat.card K : ℤ) ^ (m * (m - 1)) * ((Nat.card K : ℤ) ^ m + 1) *
        ∏ i ∈ Finset.Icc 1 (m - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
    push_cast [Nat.cast_prod]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Nat.cast_sub (h1 i)]
    push_cast
    ring
  exact_mod_cast h.trans hcast.symm

theorem ordProj_le_of_dvd_two_mul {o f : ℕ} (hf : 1 ≤ f) (h : o ∣ 2 * f) :
    ordProj[2] o ≤ 4 * ordProj[2] f := by
  have h3 := Nat.ordProj_dvd_ordProj_of_dvd (by omega : 2 * f ≠ 0) h 2
  have h4 : ordProj[2] (2 * f) = 2 * ordProj[2] f := by
    rw [Nat.ordProj_mul 2 (by norm_num) (by omega), Nat.Prime.factorization_self Nat.prime_two,
      pow_one]
  have h5 := Nat.le_of_dvd (by rw [h4]; positivity) h3
  have h6 : 0 < ordProj[2] f := Nat.ordProj_pos f 2
  omega

theorem omegaMinus_two_model_facts {B : Type} [Group B] {f : ℕ} (hf : 2 ≤ f)
    (hB : IsOmegaMinus 2 (2 ^ f) B) :
    IsSimpleGroup B ∧ Nat.card B = ordTwistedD 2 (2 ^ f) ∧
      ordProj[2] (Nat.card (Outer B)) ≤ 4 * ordProj[2] f := by
  obtain ⟨K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hB
  haveI := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  obtain ⟨F, _, _, hF, ⟨eF⟩⟩ := exists_statedOmega_quadMinus_two_mulEquiv (K := K) hirr
  have hSL : IsSLModel 2 (2 ^ (2 * f)) B :=
    ⟨F, inferInstance, inferInstance, by rw [hF, hK, ← pow_mul, mul_comm], ⟨e.trans eF⟩⟩
  obtain ⟨hs, -, hO⟩ := sl2_model_facts (by omega) hSL
  refine ⟨hs, ?_, ordProj_le_of_dvd_two_mul (by omega) hO⟩
  rw [Nat.card_congr e.toEquiv, card_statedOmega_minus_eq_ordTwistedD le_rfl hirr, hK]

theorem omegaMinus_three_model_facts {B : Type} [Group B] {f : ℕ} (hf : 2 ≤ f)
    (hB : IsOmegaMinus 3 (2 ^ f) B) :
    IsSimpleGroup B ∧ Nat.card B = ordTwistedD 3 (2 ^ f) ∧
      ordProj[2] (Nat.card (Outer B)) ≤ 4 * ordProj[2] f := by
  obtain ⟨K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hB
  haveI := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨F, _, _, hF, ⟨eF⟩⟩ := exists_statedOmega_quadMinus_three_mulEquiv (K := K) hK hirr
  have hg : Nat.gcd 4 (2 ^ f + 1) = 1 := by
    have h1 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    exact Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr (by rw [Nat.odd_iff]; omega))
  have hsc : (StatedScalars (Fin 4) F).subgroupOf (StatedSU 4 (2 ^ f) F) = ⊥ := by
    rw [← Subgroup.card_eq_one, CFSG.GH74.Generic.S1.card_scalars_statedSU_four Nat.prime_two
      (by omega) hF, hg]
  let eP : StatedProj (StatedSU 4 (2 ^ f) F) ≃* ↥(StatedSU 4 (2 ^ f) F) :=
    (QuotientGroup.quotientMulEquivOfEq hsc).trans QuotientGroup.quotientBot
  have h : StatedClassicalModel B .PSU 4 2 f :=
    ⟨⟨Nat.prime_two, by omega, by norm_num, by simp⟩, F, inferInstance, inferInstance, hF,
      ⟨(e.trans eF).trans eP.symm⟩⟩
  obtain ⟨hs, -, -⟩ := endg_omegaMinus_facts hK4 (by norm_num : 2 ≤ 3) hirr
  haveI := hs
  refine ⟨MulEquiv.isSimpleGroup e, ?_, ?_⟩
  · rw [Nat.card_congr e.toEquiv, card_statedOmega_minus_eq_ordTwistedD (by norm_num) hirr, hK]
  · have h2 := (LocalAnalysis.ComponentInitial.unitary_model_outer_two_part_bound B 4 2 f h).2.2.1
    rw [hg, mul_one] at h2
    exact ordProj_le_of_dvd_two_mul (by omega) (h2 ▸ dvd_rfl)

theorem ordD_two_eq_of_even {q : ℕ} (hq : Even q) (hq0 : 0 < q) :
    ordD 2 q = q ^ 2 * ((q ^ 2 - 1) * (q ^ 2 - 1)) := by
  have hq1 : Odd (q ^ 2 - 1) := by
    obtain ⟨r, rfl⟩ := hq
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · omega
    · have : 1 ≤ (r + r) ^ 2 := Nat.one_le_pow _ _ (by omega)
      rw [Nat.odd_iff]
      have h2 : 2 ∣ (r + r) ^ 2 := dvd_pow (by omega) (by norm_num)
      omega
  rw [ordD, Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hq1), Nat.div_one,
    show Finset.Icc 1 (2 - 1) = {1} by decide, Finset.prod_singleton]
  ring_nf

theorem ordTwistedD_two_eq_of_even {q : ℕ} (hq : Even q) :
    ordTwistedD 2 q = q ^ 2 * ((q ^ 2 + 1) * (q ^ 2 - 1)) := by
  rw [ordTwistedD_eq_of_even (by norm_num) hq, show Finset.Icc 1 (2 - 1) = {1} by decide,
    Finset.prod_singleton]
  ring_nf

theorem not_dvd_ordTrialityD4_plus {f : ℕ} (hf : 2 ≤ f) :
    ¬ (2 ^ f) ^ 9 * (2 ^ f * ((2 ^ f) ^ 2 - 1) * ordD 2 (2 ^ f)) ∣ ordTrialityD4 (2 ^ f) := by
  intro h
  set q := 2 ^ f with hq
  have hev : Even q := (Nat.even_pow' (by omega)).mpr even_two
  have hq4 : 4 ≤ q := by
    rw [hq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  rw [ordD_two_eq_of_even hev (by positivity), ordTrialityD4] at h
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hz := Int.natCast_dvd_natCast.mpr h
  push_cast [Nat.cast_sub h1, Nat.cast_sub h6] at hz
  have hne : ((q : ℤ) ^ 12 * ((q : ℤ) ^ 2 - 1) ^ 2) ≠ 0 := by
    have : (4 : ℤ) ≤ q := by exact_mod_cast hq4
    have h2 : (q : ℤ) ^ 2 - 1 ≠ 0 := by nlinarith
    positivity
  have e1 : (q : ℤ) ^ 9 * ((q : ℤ) * ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 2 * (((q : ℤ) ^ 2 - 1) *
      ((q : ℤ) ^ 2 - 1)))) = ((q : ℤ) ^ 12 * ((q : ℤ) ^ 2 - 1) ^ 2) * ((q : ℤ) ^ 2 - 1) := by ring
  have e2 : (q : ℤ) ^ 12 * ((q : ℤ) ^ 8 + (q : ℤ) ^ 4 + 1) * ((q : ℤ) ^ 6 - 1) *
      ((q : ℤ) ^ 2 - 1) = ((q : ℤ) ^ 12 * ((q : ℤ) ^ 2 - 1) ^ 2) *
        (((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 10 + 2 * (q : ℤ) ^ 8 + 4 * (q : ℤ) ^ 6 +
          5 * (q : ℤ) ^ 4 + 7 * (q : ℤ) ^ 2 + 8) + 9) := by ring
  rw [e1, e2, mul_dvd_mul_iff_left hne] at hz
  have h9 := (dvd_add_right (dvd_mul_right _ _)).mp hz
  have hle := Int.le_of_dvd (by norm_num) h9
  have : (4 : ℤ) ≤ q := by exact_mod_cast hq4
  nlinarith

theorem not_dvd_ordTrialityD4_minus {f : ℕ} (hf : 1 ≤ f) :
    ¬ (2 ^ f) ^ 9 * (2 ^ f * ((2 ^ f) ^ 2 - 1) * ordTwistedD 2 (2 ^ f)) ∣
      ordTrialityD4 (2 ^ f) := by
  intro h
  set q := 2 ^ f with hq
  have hev : Even q := (Nat.even_pow' (by omega)).mpr even_two
  have hq2 : 2 ≤ q := by
    rw [hq]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  rw [ordTwistedD_two_eq_of_even hev, ordTrialityD4] at h
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h6 : 1 ≤ q ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hz := Int.natCast_dvd_natCast.mpr h
  push_cast [Nat.cast_sub h1, Nat.cast_sub h6] at hz
  have hne : ((q : ℤ) ^ 12 * ((q : ℤ) ^ 2 - 1) ^ 2) ≠ 0 := by
    have : (2 : ℤ) ≤ q := by exact_mod_cast hq2
    have h2 : (q : ℤ) ^ 2 - 1 ≠ 0 := by nlinarith
    positivity
  have e1 : (q : ℤ) ^ 9 * ((q : ℤ) * ((q : ℤ) ^ 2 - 1) * ((q : ℤ) ^ 2 * (((q : ℤ) ^ 2 + 1) *
      ((q : ℤ) ^ 2 - 1)))) = ((q : ℤ) ^ 12 * ((q : ℤ) ^ 2 - 1) ^ 2) * ((q : ℤ) ^ 2 + 1) := by ring
  have e2 : (q : ℤ) ^ 12 * ((q : ℤ) ^ 8 + (q : ℤ) ^ 4 + 1) * ((q : ℤ) ^ 6 - 1) *
      ((q : ℤ) ^ 2 - 1) = ((q : ℤ) ^ 12 * ((q : ℤ) ^ 2 - 1) ^ 2) *
        (((q : ℤ) ^ 2 + 1) * ((q : ℤ) ^ 10 + 2 * (q : ℤ) ^ 6 - (q : ℤ) ^ 4 +
          3 * (q : ℤ) ^ 2 - 2) + 3) := by ring
  rw [e1, e2, mul_dvd_mul_iff_left hne] at hz
  have h3 := (dvd_add_right (dvd_mul_right _ _)).mp hz
  have hle := Int.le_of_dvd (by norm_num) h3
  have : (2 : ℤ) ≤ q := by exact_mod_cast hq2
  nlinarith

theorem card_of_lieModel_trialityD4 {X : Type} [Group X] {k f : ℕ}
    (h : LieModel X .trialityD4 k 2 f) : Nat.card X = ordTrialityD4 (2 ^ f) := by
  rcases h with ⟨ht, -⟩ | ⟨-, -, hm⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
  · exact absurd ht (by decide)
  · exact Timmesfeld.card_chevalleyExceptionalModel_two hm
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)

end CFSG.RankThree.GF2n.Smith81.Insp
