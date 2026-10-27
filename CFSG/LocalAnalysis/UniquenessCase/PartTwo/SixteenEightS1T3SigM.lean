module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.LocalAnalysis.ComponentClassification.SolAltLitSol78Inputs
public import CFSG.Open.GriessAllModelsStatement
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKOmegaPlusSix
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Cover

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

@[simp] private theorem s16t3_card_multiplicative_zmod (x : ℕ) :
    Nat.card (Multiplicative (ZMod x)) = x :=
  (Nat.card_congr (Multiplicative.toAdd (α := ZMod x))).trans (Nat.card_zmod x)

private theorem s16t3_card_generic_exceptional (t : CFSG.Assembly.LowTwoRank.StatedLieTag)
    (n p f : ℕ) :
    Nat.card (CFSG.Blueprint.Multiplier.generic t n p f ×
      CFSG.Blueprint.Multiplier.exceptional t n p f) =
      (CFSG.Blueprint.Multiplier.genericOrders t n p f).1 *
        (CFSG.Blueprint.Multiplier.genericOrders t n p f).2 *
        ((CFSG.Blueprint.Multiplier.exceptionalOrders t n p f).1 *
          (CFSG.Blueprint.Multiplier.exceptionalOrders t n p f).2) := by
  simp [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional,
    Nat.card_prod]

private theorem s16t3_two_pow_card_generic_exceptional
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ}
    (hg : CFSG.Blueprint.Multiplier.genericOrders t n p f = (1, 1))
    (he : CFSG.Blueprint.Multiplier.exceptionalOrders t n p f = (1, 1) ∨
      CFSG.Blueprint.Multiplier.exceptionalOrders t n p f = (2, 1) ∨
      CFSG.Blueprint.Multiplier.exceptionalOrders t n p f = (2, 2)) :
    ∃ k, Nat.card (CFSG.Blueprint.Multiplier.generic t n p f ×
      CFSG.Blueprint.Multiplier.exceptional t n p f) = 2 ^ k := by
  rcases he with he | he | he
  · exact ⟨0, by rw [s16t3_card_generic_exceptional, hg, he]; norm_num⟩
  · exact ⟨1, by rw [s16t3_card_generic_exceptional, hg, he]; norm_num⟩
  · exact ⟨2, by rw [s16t3_card_generic_exceptional, hg, he]; norm_num⟩

private theorem s16t3_genericOrders_psl (n : ℕ) :
    CFSG.Blueprint.Multiplier.genericOrders .PSL n 2 1 = (1, 1) := by
  simp [CFSG.Blueprint.Multiplier.genericOrders]

private theorem s16t3_genericOrders_psp (n : ℕ) :
    CFSG.Blueprint.Multiplier.genericOrders .PSp n 2 1 = (1, 1) := by
  simp [CFSG.Blueprint.Multiplier.genericOrders]

private theorem s16t3_genericOrders_pomegaPlus (n : ℕ) :
    CFSG.Blueprint.Multiplier.genericOrders .POmegaPlus n 2 1 = (1, 1) := by
  simp [CFSG.Blueprint.Multiplier.genericOrders]

private theorem s16t3_genericOrders_pomegaMinus (n : ℕ) (hn : n ≠ 0) :
    CFSG.Blueprint.Multiplier.genericOrders .POmegaMinus n 2 1 = (1, 1) := by
  have heven : Even (2 ^ n) := by
    rw [Nat.even_pow]
    exact ⟨even_two, hn⟩
  have hodd : Odd (2 ^ n + 1) := by
    refine Nat.odd_iff.mpr (Nat.not_even_iff.mp ?_)
    rw [Nat.even_add_one]
    exact fun h => h heven
  have hgcd : Nat.gcd 4 (2 ^ n + 1) = 1 := by
    have h2 : Nat.Coprime 2 (2 ^ n + 1) := Nat.coprime_two_left.mpr hodd
    have h4 : Nat.Coprime (2 ^ 2) (2 ^ n + 1) := h2.pow_left 2
    simpa using h4
  simp [CFSG.Blueprint.Multiplier.genericOrders, hgcd]

private theorem s16t3_genericOrders_psu_four :
    CFSG.Blueprint.Multiplier.genericOrders .PSU 4 2 1 = (1, 1) := by
  decide

private theorem s16t3_exceptionalOrders_psl (n : ℕ) (hn : 4 ≤ n) :
    CFSG.Blueprint.Multiplier.exceptionalOrders .PSL n 2 1 = (1, 1) ∨
    CFSG.Blueprint.Multiplier.exceptionalOrders .PSL n 2 1 = (2, 1) ∨
    CFSG.Blueprint.Multiplier.exceptionalOrders .PSL n 2 1 = (2, 2) := by
  rcases eq_or_lt_of_le hn with rfl | hn5
  · exact Or.inr (Or.inl (by decide))
  · refine Or.inl ?_
    unfold CFSG.Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all <;> omega

private theorem s16t3_exceptionalOrders_psp (n : ℕ) (hn : 3 ≤ n) :
    CFSG.Blueprint.Multiplier.exceptionalOrders .PSp n 2 1 = (1, 1) ∨
    CFSG.Blueprint.Multiplier.exceptionalOrders .PSp n 2 1 = (2, 1) ∨
    CFSG.Blueprint.Multiplier.exceptionalOrders .PSp n 2 1 = (2, 2) := by
  rcases eq_or_lt_of_le hn with rfl | hn4
  · exact Or.inr (Or.inl (by decide))
  · refine Or.inl ?_
    unfold CFSG.Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all <;> omega

private theorem s16t3_exceptionalOrders_pomegaPlus (n : ℕ) (hn : 4 ≤ n) :
    CFSG.Blueprint.Multiplier.exceptionalOrders .POmegaPlus n 2 1 = (1, 1) ∨
    CFSG.Blueprint.Multiplier.exceptionalOrders .POmegaPlus n 2 1 = (2, 1) ∨
    CFSG.Blueprint.Multiplier.exceptionalOrders .POmegaPlus n 2 1 = (2, 2) := by
  rcases eq_or_lt_of_le hn with rfl | hn5
  · exact Or.inr (Or.inr (by decide))
  · refine Or.inl ?_
    unfold CFSG.Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all <;> omega

private theorem s16t3_exceptionalOrders_pomegaMinus (n : ℕ) :
    CFSG.Blueprint.Multiplier.exceptionalOrders .POmegaMinus n 2 1 = (1, 1) ∨
    CFSG.Blueprint.Multiplier.exceptionalOrders .POmegaMinus n 2 1 = (2, 1) ∨
    CFSG.Blueprint.Multiplier.exceptionalOrders .POmegaMinus n 2 1 = (2, 2) := by
  refine Or.inl ?_
  unfold CFSG.Blueprint.Multiplier.exceptionalOrders
  split <;> simp_all <;> omega

private theorem s16t3_exceptionalOrders_psu_four :
    CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 4 2 1 = (1, 1) ∨
    CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 4 2 1 = (2, 1) ∨
    CFSG.Blueprint.Multiplier.exceptionalOrders .PSU 4 2 1 = (2, 2) :=
  Or.inr (Or.inl (by decide))

private theorem s16t3_statedClassicalModel_statedSL_two {K : Type} [Field K] [Finite K]
    {n : ℕ} (hn : 3 ≤ n) (hK : Nat.card K = 2) :
    StatedClassicalModel (StatedSL n K) .PSL n 2 1 := by
  have hbot : (StatedScalars (Fin n) K).subgroupOf (StatedSL n K) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hg
    have hc1 : c = 1 := by
      have hsub : Subsingleton Kˣ :=
        (Nat.card_eq_one_iff_unique.mp (by simp [Nat.card_units, hK])).1
      exact hsub.allEq c 1
    exact Subtype.ext (by rw [← hc, hc1, map_one]; rfl)
  have hproj : StatedProj (StatedSL n K) ≃* StatedSL n K :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  refine ⟨⟨Nat.prime_two, le_refl 1, by omega, ?_, ?_⟩, K, inferInstance, inferInstance,
    by rw [hK]; norm_num, ⟨hproj.symm⟩⟩
  · rintro h; exact absurd (congrArg Prod.fst h) (by omega)
  · rintro h; exact absurd (congrArg Prod.snd h) (by norm_num)

private theorem s16t3_statedClassicalModel_statedSp_two {K : Type} [Field K] [Finite K]
    {n : ℕ} (hn : 3 ≤ n) (hK : Nat.card K = 2) :
    StatedClassicalModel (StatedSp n K) .PSp n 2 1 := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime (p := 2)
    (by rw [Fintype.card_eq_nat_card, hK])
  have hbot := CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot (K := K) (n := n)
  have hproj : StatedProj (StatedSp n K) ≃* StatedSp n K :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  refine ⟨⟨Nat.prime_two, le_refl 1, by omega, ?_⟩, K, inferInstance, inferInstance,
    by rw [hK]; norm_num, ⟨hproj.symm⟩⟩
  rintro h
  exact absurd (congrArg Prod.fst h) (by omega)

private theorem s16t3_two_pow_of_lieModel (hGA : CFSG.Open.GriessAllModelsStatement)
    {X : Type} [Group X] {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ}
    (hmodel : CFSG.Models.LieModel X t n p f)
    (hcard : ∃ k, Nat.card (CFSG.Blueprint.Multiplier.generic t n p f ×
      CFSG.Blueprint.Multiplier.exceptional t n p f) = 2 ^ k) :
    ∃ k, Nat.card (CFSG.Open.griessHopfMultiplier X) = 2 ^ k := by
  obtain ⟨-, ⟨m⟩⟩ := hGA X t n p f hmodel
  obtain ⟨k, hk⟩ := hcard
  exact ⟨k, by rw [Nat.card_congr m.toEquiv, hk]⟩

private theorem s16t3_alt_mult
    (hSchur : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    {X : Type} [Group X] {n : ℕ} (hX : UC22.IsAlt X n) (hn : 8 ≤ n) :
    ∃ k : ℕ, Nat.card (CFSG.Open.griessHopfMultiplier X) = 2 ^ k := by
  obtain ⟨e⟩ := hX
  have hcard : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier
      (alternatingGroup (Fin n))) = 2 := by
    have h := (hSchur n (by omega)).2
    rwa [if_neg (by omega : ¬ (n = 6 ∨ n = 7))] at h
  refine ⟨1, ?_⟩
  rw [Nat.card_congr (CFSG.LieType.Steinberg.CentralExt.griessHopfMultiplierCongr e).toEquiv,
    Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess
      (alternatingGroup (Fin n))).toEquiv]
  simpa using hcard

theorem s16t3_card_mult_eq_two_pow_of_shape (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSchur : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    {X : Type} [Group X] {n : ℕ}
    (hX : (IsSLn X n 1 ∧ 4 ≤ n) ∨ (IsSpn X n 1 ∧ 6 ≤ n) ∨ (IsOmegaPlus X n 1 ∧ 6 ≤ n) ∨
      (IsOmegaMinus X n 1 ∧ 6 ≤ n) ∨ (UC22.IsAlt X n ∧ 8 ≤ n)) :
    ∃ k : ℕ, Nat.card (CFSG.Open.griessHopfMultiplier X) = 2 ^ k := by
  rcases hX with ⟨hSL, hn4⟩ | ⟨hSp, hn6⟩ | ⟨hOP, hn6⟩ | ⟨hOM, hn6⟩ | ⟨hAlt, hn8⟩
  · obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hSL
    letI : Field K := hKf
    letI : Finite K := hKfin
    have hK2 : Nat.card K = 2 := by rw [hKcard]; norm_num
    have hclass : StatedClassicalModel X .PSL n 2 1 :=
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm
        (s16t3_statedClassicalModel_statedSL_two (n := n) (by omega) hK2)
    have hmodel : CFSG.Models.LieModel X .PSL n 2 1 := ⟨hclass.1, Or.inl hclass⟩
    exact s16t3_two_pow_of_lieModel hGA hmodel
      (s16t3_two_pow_card_generic_exceptional (s16t3_genericOrders_psl n)
        (s16t3_exceptionalOrders_psl n hn4))
  · obtain ⟨hEven, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hSp
    letI : Field K := hKf
    letI : Finite K := hKfin
    have hK2 : Nat.card K = 2 := by rw [hKcard]; norm_num
    have hn3 : 3 ≤ n / 2 := by omega
    have hclass : StatedClassicalModel X .PSp (n / 2) 2 1 :=
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm
        (s16t3_statedClassicalModel_statedSp_two (n := n / 2) hn3 hK2)
    have hmodel : CFSG.Models.LieModel X .PSp (n / 2) 2 1 := ⟨hclass.1, Or.inl hclass⟩
    exact s16t3_two_pow_of_lieModel hGA hmodel
      (s16t3_two_pow_card_generic_exceptional (s16t3_genericOrders_psp (n / 2))
        (s16t3_exceptionalOrders_psp (n / 2) hn3))
  · by_cases h6 : n = 6
    · subst h6
      exact s16t3_alt_mult hSchur (s15k_omp6_isAlt8 hOP) (by norm_num)
    · obtain ⟨hEven, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hOP
      letI : Field K := hKf
      letI : Finite K := hKfin
      obtain ⟨m, hm⟩ := hEven
      have hn4 : 4 ≤ n / 2 := by omega
      have hclass : StatedClassicalModel X .POmegaPlus (n / 2) 2 1 :=
        ⟨⟨Nat.prime_two, le_refl 1, hn4⟩, K, inferInstance, inferInstance, hKcard, ⟨e⟩⟩
      have hmodel : CFSG.Models.LieModel X .POmegaPlus (n / 2) 2 1 :=
        ⟨hclass.1, Or.inl hclass⟩
      exact s16t3_two_pow_of_lieModel hGA hmodel
        (s16t3_two_pow_card_generic_exceptional (s16t3_genericOrders_pomegaPlus (n / 2))
          (s16t3_exceptionalOrders_pomegaPlus (n / 2) hn4))
  · by_cases h6 : n = 6
    · subst h6
      have hU4 : IsU4 X 1 := isU4_of_isOmegaMinus_six hOM
      have hclass : StatedClassicalModel X .PSU 4 2 1 :=
        CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num : (4 : ℕ) ≠ 0)
          hU4
      have hmodel : CFSG.Models.LieModel X .PSU 4 2 1 := ⟨hclass.1, Or.inl hclass⟩
      exact s16t3_two_pow_of_lieModel hGA hmodel
        (s16t3_two_pow_card_generic_exceptional s16t3_genericOrders_psu_four
          s16t3_exceptionalOrders_psu_four)
    · obtain ⟨hEven, K, hKf, hKfin, b, c, hKcard, hirr, ⟨e⟩⟩ := hOM
      letI : Field K := hKf
      letI : Finite K := hKfin
      obtain ⟨m, hm⟩ := hEven
      have hn4 : 4 ≤ n / 2 := by omega
      have hclass : StatedClassicalModel X .POmegaMinus (n / 2) 2 1 :=
        ⟨⟨Nat.prime_two, le_refl 1, hn4⟩, K, inferInstance, inferInstance, hKcard, b, c, hirr,
          ⟨e⟩⟩
      have hmodel : CFSG.Models.LieModel X .POmegaMinus (n / 2) 2 1 :=
        ⟨hclass.1, Or.inl hclass⟩
      exact s16t3_two_pow_of_lieModel hGA hmodel
        (s16t3_two_pow_card_generic_exceptional
          (s16t3_genericOrders_pomegaMinus (n / 2) (by omega))
          (s16t3_exceptionalOrders_pomegaMinus (n / 2)))
  · exact s16t3_alt_mult hSchur hAlt hn8

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
