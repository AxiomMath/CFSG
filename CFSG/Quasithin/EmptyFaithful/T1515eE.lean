module

public import CFSG.Quasithin.EmptyFaithful.T1515eD
public import CFSG.Quasithin.EmptyFaithful.T1515eB
public import CFSG.Quasithin.Background.A3FactsTrialityTwo
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAlternatingExclusion
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalLinearFourTwo
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineGroups

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin.A3Facts

theorem l34NotL42Fact1515e_of_cert : L34NotL42Fact1515e := by
  intro X _ h3 h4
  obtain ⟨e⟩ := (CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff X).mp
    (Or.inl ⟨by decide, h4⟩)
  exact ((CFSG.ComponentClassification.PSL3Four.excludes_alternating_models_stated X h3).2.2
    (Fin 8) (by simp)).false e

open Polynomial in
theorem pow_three_eq_one_of_pow_three_pow1515e {K : Type} [Field K] [CharP K 3]
    (A : Matrix (Fin 3) (Fin 3) K) (k : ℕ) (hA : A ^ (3 ^ k) = 1) : A ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : (X - 1 : K[X]) ^ (3 ^ k) = X ^ (3 ^ k) - 1 := by
    simpa using sub_pow_char_pow (R := K[X]) (p := 3) (X : K[X]) 1 k
  have h2 : (X - 1 : K[X]) ^ 3 = X ^ 3 - 1 := by
    simpa using sub_pow_char (R := K[X]) (p := 3) (X : K[X]) 1
  have hN : (A - 1) ^ (3 ^ k) = 0 := by
    have := congrArg (Polynomial.aeval A) h1
    simpa [hA, map_pow, map_sub] using this
  have hnil : IsNilpotent (A - 1) := ⟨3 ^ k, hN⟩
  have hcp : (A - 1).charpoly = X ^ 3 := by
    have h := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hnil
    rw [Fintype.card_fin] at h
    exact sub_eq_zero.mp (IsNilpotent.eq_zero h)
  have hN3 : (A - 1) ^ 3 = 0 := by
    have := Matrix.aeval_self_charpoly (A - 1)
    rw [hcp] at this
    simpa using this
  have := congrArg (Polynomial.aeval A) h2
  simp only [map_pow, map_sub, aeval_X, map_one] at this
  rw [hN3] at this
  exact sub_eq_zero.mp this.symm

theorem pow_three_eq_one_of_isPGroup1515e {K : Type} [Field K] [CharP K 3] {H : Type} [Group H]
    (ι : H →* GL (Fin 3) K) (hι : Function.Injective ι) (hH : IsPGroup 3 H) (g : H) :
    g ^ 3 = 1 := by
  obtain ⟨k, hk⟩ := hH g
  have h1 : ((ι g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ (3 ^ k) = 1 := by
    have := congrArg (fun x : H => ((ι x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hk
    simpa [map_pow] using this
  have h3 := pow_three_eq_one_of_pow_three_pow1515e _ k h1
  apply hι
  apply Units.ext
  simpa [map_pow] using h3

open CFSG.LinearGroups.UnitaryThreeOverNine in
theorem two_le_pRank_statedSU_three_three1515e {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 9) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedSU 3 3 K)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := Fintype.ofFinite K
  have hch : CharP K 3 := charP_of_card_eq_prime_pow (p := 3) (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
  have hfin : Finite (StatedSU 3 3 K) := Nat.finite_of_card_ne_zero (by
    rw [card_statedSU hK]; norm_num)
  let P : Sylow 3 (StatedSU 3 3 K) := default
  have h9 : 3 ^ 2 ∣ Nat.card (P : Subgroup (StatedSU 3 3 K)) :=
    P.pow_dvd_card_of_pow_dvd_card (by rw [card_statedSU hK]; norm_num)
  refine two_le_pRank_of_not_isCyclic (by norm_num) (P := (P : Subgroup (StatedSU 3 3 K)))
    P.isPGroup' ?_
  intro hcyc
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hord : orderOf g = Nat.card (P : Subgroup (StatedSU 3 3 K)) :=
    orderOf_eq_card_of_forall_mem_zpowers hg
  have hg3 : g ^ 3 = 1 :=
    pow_three_eq_one_of_isPGroup1515e
      ((StatedSU 3 3 K).subtype.comp (P : Subgroup (StatedSU 3 3 K)).subtype)
      ((Subtype.val_injective).comp (Subtype.val_injective)) P.isPGroup' g
  have hdvd : Nat.card (P : Subgroup (StatedSU 3 3 K)) ∣ 3 := hord ▸ orderOf_dvd_of_pow_eq_one hg3
  have hpos : 0 < Nat.card (P : Subgroup (StatedSU 3 3 K)) := Nat.card_pos
  have := Nat.le_of_dvd (by norm_num) (dvd_trans h9 hdvd)
  omega

open CFSG.LinearGroups.UnitaryThreeOverNine in
theorem two_le_pRank_of_isPSU_three_three1515e {X : Type} [Group X] [Finite X]
    (h : IsPSU 3 3 1 X) : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  obtain ⟨-, K, _, hKfin, hK, ⟨e⟩⟩ := h
  have hK9 : Nat.card K = 9 := by rw [hK]; norm_num
  have e' : X ≃* StatedSU 3 3 K :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq
      (statedScalars_subgroupOf_statedSU_eq_bot hK9)).trans QuotientGroup.quotientBot)
  have hfin : Finite (StatedSU 3 3 K) := Nat.finite_of_card_ne_zero (by
    rw [card_statedSU hK9]; norm_num)
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e']
  exact two_le_pRank_statedSU_three_three1515e hK9

theorem two_le_pRank_quasithinTrialityD4Two_three1515e :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup CFSG.Open.quasithinTrialityD4Two) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (GL (Fin 8) (GaloisField 2 3)) :=
    Finite.of_injective Units.val Units.val_injective
  refine two_le_pRank_of_gens
    (x := (⟨d4ψ d4X, d4ψ_X_mem⟩ : CFSG.Open.quasithinTrialityD4Two))
    (y := (⟨d4ψ d4Y, d4ψ_Y_mem⟩ : CFSG.Open.quasithinTrialityD4Two)) ?_ ?_ ?_ ?_ ?_
  · refine Subtype.ext ?_
    change d4ψ d4X ^ 3 = 1
    rw [← map_pow, d4X_pow_three, map_one]
  · refine Subtype.ext ?_
    change d4ψ d4Y ^ 3 = 1
    rw [← map_pow, d4Y_pow_three, map_one]
  · refine Subtype.ext ?_
    change d4ψ d4X * d4ψ d4Y = d4ψ d4Y * d4ψ d4X
    rw [← map_mul, ← map_mul, d4X_comm]
  · intro h
    refine d4X_ne_one (d4ψ_injective ?_)
    have h' := congrArg Subtype.val h
    change d4ψ d4X = 1 at h'
    rw [h', map_one]
  · intro n h
    refine d4X_pow_ne n (d4ψ_injective ?_)
    have h' := congrArg Subtype.val h
    change d4ψ d4X ^ n = d4ψ d4Y at h'
    rw [← map_pow] at h'
    exact h'

theorem two_le_pRank_of_is3D4_two1515e
    {X : Type} [Group X] [Finite X] (h : Is3D4 2 1 X) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  have hL : LieModel X .trialityD4 0 2 1 := Or.inr (Or.inl ⟨rfl, by decide, h⟩)
  obtain ⟨e⟩ := trialityD4ModelBridge_of_lieModel X hL
  have : Finite (GL (Fin 8) (GaloisField 2 3)) :=
    Finite.of_injective Units.val Units.val_injective
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
  exact two_le_pRank_quasithinTrialityD4Two_three1515e

theorem knownFacts15122Types_final
    : KnownFacts15122Types :=
  knownFacts15122Types_of l34NotL42Fact1515e_of_cert
    (fun _ _ _ h => two_le_pRank_of_isPSU_three_three1515e h)
    (fun _ _ _ h => two_le_pRank_of_is3D4_two1515e h)

theorem Lemma15125InputRestU.toFive (h : Lemma15125InputRestU) : Lemma15125InputFive :=
  fun G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL h22 h24 =>
    (h G T Mc M Z₁ Z₂ V₁ V₂ L hC h17 h18 h19 hL h22 h24).2.2

theorem lemma15125InputRestU_of_five_final
    (hF : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK) (h5 : Lemma15125InputFive) :
    Lemma15125InputRestU :=
  lemma15125InputRestU_of_five hF h36 h38 knownFacts15122Types_final h5

theorem theorem1515_of_inputs_ce4
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h36 : A36ForSQTK) (hF : A318Facts)
    (h23 : Lemma15123Standalone)
    (h316 : Theorem316Statement) (h317 : Theorem317Statement) (h319 : Lemma319Statement)
    (h1414 : StageLemma1414) (h1416 : StageLemma1416) (h1417 : StageLemma1417)
    (hD : Description1512CE) (hN : Nilpotency1512CE) (hStep : Step1514Gen)
    (h17 : StageLemma1517) (h158 : StageLemma1518) (h1511one : StageLemma15111One)
    (h1512four : StageLemma15112Four)
    (hI20 : Lemma15120InputU) (hI21 : Lemma15121InputU) (hI22 : Lemma15122InputU)
    (hI24 : Lemma15124InputU) (h5 : Lemma15125InputFive) (hI27 : Lemma15127InputU)
    (hI28 : Lemma15128InputU) (hI29 : Lemma15129InputU) : StageTheorem1515 :=
  theorem1515_of_inputs_ce3 h37 h38 h39 h23 h316 h317 h319 h1414 h1416 h1417 hD hN hStep h17 h158
    h1511one h1512four hI20 hI21 hI22 hI24 (lemma15125InputRestU_of_five_final hF h36 h38 h5) hI27
    hI28 hI29

end CFSG.Quasithin
