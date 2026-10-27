module

public import CFSG.RankThree.PartOne.TAIL.KSideCen
public import CFSG.RankThree.PartOne.FLM.Model

public section

namespace CFSG.RankThree.PartOne.TAIL

open CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.PerfectCover CFSG.Timmesfeld
open CFSG.RankThree.PartOne.S12K (charTwoOrder card_of_lieModel_two)
open CFSG.RankThree.PartOne.FLM (statedClassicalModel_psl_of_mulEquiv)

theorem center_eq_bot_of_psl_eight {E : Type} [Group E]
    (h : StatedClassicalModel E .PSL 2 2 3) : Subgroup.center E = ⊥ := by
  obtain ⟨-, hs⟩ := CFSG.LieType.Simplicity.fam_PSL_simplicity E 2 2 3 h
  have hcard : Nat.card E = CFSG.Open.ordA (2 - 1) (2 ^ 3) :=
    (card_statedClassicalModel_two h).1 rfl
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center E) with h0 | h0
  · exact h0
  · exfalso
    have hc : IsMulCommutative E := Subgroup.center_eq_top_iff.1 h0
    have hp := Group.is_simple_iff_prime_card.1 hs
    rw [hcard, show CFSG.Open.ordA (2 - 1) (2 ^ 3) = 504 by decide] at hp
    exact absurd hp (by norm_num)

theorem card_multiplier_psl_two_twentyone :
    Nat.card (Blueprint.Multiplier.generic .PSL 2 2 21 ×
      Blueprint.Multiplier.exceptional .PSL 2 2 21) = 1 := by
  have hgen : Blueprint.Multiplier.genericOrders .PSL 2 2 21 = (1, 1) := by
    change (Nat.gcd 2 (2 ^ 21 - 1), 1) = (1, 1)
    decide
  have hexc : Blueprint.Multiplier.exceptionalOrders .PSL 2 2 21 = (1, 1) := rfl
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
  rw [hgen, hexc]
  simp

theorem center_eq_bot_of_psl_of_trivial
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {X : Type} [Group X] [Finite X] {n f : ℕ} (hperf : Group.IsPerfect X)
    (hmodel : StatedClassicalModel (X ⧸ Subgroup.center X) .PSL n 2 f)
    (htriv : Nat.card (Blueprint.Multiplier.generic .PSL n 2 f ×
      Blueprint.Multiplier.exceptional .PSL n 2 f) = 1) :
    Subgroup.center X = ⊥ := by
  have hm' : Models.LieModel (X ⧸ Subgroup.center X) .PSL n 2 f := ⟨hmodel.1, .inl hmodel⟩
  obtain ⟨hperf', hcard⟩ := card_hopfMultiplier_of_model hGA hm'
  have hd := card_ker_dvd_card_hopfMultiplier hperf' hperf (QuotientGroup.mk' (Subgroup.center X))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk'])
  rw [QuotientGroup.ker_mk', hcard, htriv] at hd
  rw [← Subgroup.card_eq_one]
  exact Nat.dvd_one.1 hd

theorem nonempty_projectiveSL_equiv_specialLinear_two {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ 21) :
    Nonempty
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F ≃* Matrix.SpecialLinearGroup (Fin 2) F) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq
    (center_sl_eq_bot (by norm_num) (by rw [hF]; norm_num))).trans QuotientGroup.quotientBot⟩

section Main

theorem field_l28_model_core
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {G : Type} [Group G] [Finite G] (K E : Subgroup G)
    (hK : CFSG.IsQuasisimple ↥K) (t : StatedLieTag) (n f : ℕ)
    (hKm : Blueprint.LieModel (↥K ⧸ Subgroup.center ↥K) t n 2 (7 * f))
    (hEm : Blueprint.LieModel (↥E ⧸ Subgroup.center ↥E) t n 2 f ∨
      (t = .twistedF4 ∧ n = 0 ∧ f = 1 ∧
        Blueprint.LieModel (↥E ⧸ Subgroup.center ↥E) .Tits 0 2 1))
    (hmod : StatedClassicalModel ↥E .PSL 2 2 3) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ 21 ∧
      Nonempty (↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  have hZE : Subgroup.center ↥E = ⊥ := center_eq_bot_of_psl_eight hmod
  let eE : ↥E ⧸ Subgroup.center ↥E ≃* ↥E :=
    (QuotientGroup.quotientMulEquivOfEq hZE).trans QuotientGroup.quotientBot
  have hcardE : Nat.card (↥E ⧸ Subgroup.center ↥E) = charTwoOrder .PSL 2 3 := by
    rw [Nat.card_congr eE.toEquiv]
    exact (card_statedClassicalModel_two hmod).1 rfl
  have hmain : t = .PSL ∧ n = 2 ∧ f = 3 := by
    rcases hEm with hEm | ⟨rfl, rfl, rfl, hT⟩
    · obtain ⟨hadm, hc⟩ := card_of_lieModel_two hEm
      exact CFSG.RankThree.PartOne.S12K.rigid_L hadm (g := 3) (by norm_num)
        (hc.symm.trans hcardE)
    · exfalso
      have hc := (card_of_lieModel_two hT).2
      exact CFSG.RankThree.PartOne.S12K.ordTits_ne_ordA_one (g := 3) (by norm_num)
        (hc.symm.trans hcardE)
  obtain ⟨rfl, rfl, rfl⟩ := hmain
  have hKmodel : StatedClassicalModel (↥K ⧸ Subgroup.center ↥K) .PSL 2 2 21 := by
    rcases hKm with ⟨-, hc⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · simpa using hc
    all_goals omega
  have hZK : Subgroup.center ↥K = ⊥ :=
    center_eq_bot_of_psl_of_trivial hGA hK.1 hKmodel card_multiplier_psl_two_twentyone
  obtain ⟨-, F, hFfield, hFfin, hFcard, ⟨e⟩⟩ := hKmodel
  obtain ⟨e2⟩ := nonempty_projectiveSL_equiv_specialLinear_two hFcard
  let eK : ↥K ⧸ Subgroup.center ↥K ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hZK).trans QuotientGroup.quotientBot
  exact ⟨F, hFfield, hFfin, hFcard, ⟨eK.symm.trans (e.trans
    ((projectiveSpecialLinearGroupEquivStatedProj 2 F).symm.trans e2))⟩⟩

theorem fieldL28Model_holds
    (hGA : CFSG.Open.GriessAllModelsStatement) :
    ∀ (G : Type) [Group G] [Finite G] (c : G) (K : Subgroup G),
      CFSG.IsQuasisimple ↥K → ¬ 7 ∣ Nat.card (Subgroup.center ↥K) → InducesFieldAut 7 c K →
      StatedClassicalModel
        ↥(inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({c} : Set G))) .PSL 2 2 3 →
        ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ 21 ∧
          Nonempty (↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  intro G _ _ c K hK _ hind hmod
  obtain ⟨-, -, -, t, n, f, -, hKm, hEm⟩ := hind
  exact field_l28_model_core hGA K _ hK t n f hKm hEm hmod

end Main

end CFSG.RankThree.PartOne.TAIL
