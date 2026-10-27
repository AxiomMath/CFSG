module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs
public import CFSG.Open.GriessAllModelsStatement
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOMinusFacts
public import CFSG.Quasithin.Vol2.GoldschmidtF431UnModel
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Orthogonal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open

private theorem s16k_charP_two_of_card_four {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) : CharP K 2 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := 2) (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)

private theorem s16k_center_statedSp_eq_bot {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 4) (n : ℕ) : Subgroup.center (StatedSp n K) = ⊥ := by
  have : CharP K 2 := s16k_charP_two_of_card_four hK
  rw [CFSG.LieType.Universal.Symplectic.center_eq,
    CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot]

private theorem s16k_statedClassicalModel_statedSp {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 2 ≤ n) (hK : Nat.card K = 4) :
    StatedClassicalModel (StatedSp n K) .PSp n 2 2 := by
  have : CharP K 2 := s16k_charP_two_of_card_four hK
  have hbot := CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot (K := K) (n := n)
  have hproj : StatedProj (StatedSp n K) ≃* StatedSp n K :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  refine ⟨⟨Nat.prime_two, by norm_num, hn, ?_⟩, K, inferInstance, inferInstance,
    by rw [hK]; norm_num, ⟨hproj.symm⟩⟩
  rintro h
  exact absurd (congrArg Prod.snd h) (by norm_num)

private theorem s16k_center_eq_bot_of_mulEquiv {X Y : Type*} [Group X] [Group Y]
    (φ : X ≃* Y) (h : Subgroup.center Y = ⊥) : Subgroup.center X = ⊥ :=
  (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center X) φ.injective).1 <| by
    rw [Subgroup.map_center_eq φ, h]

private theorem s16k_card_generic_exceptional_psp_two :
    Nat.card (CFSG.Blueprint.Multiplier.generic .PSp 2 2 2 ×
      CFSG.Blueprint.Multiplier.exceptional .PSp 2 2 2) = 1 := by
  simp only [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional,
    CFSG.Blueprint.Multiplier.genericOrders, CFSG.Blueprint.Multiplier.exceptionalOrders,
    Nat.card_prod]
  norm_num [ZMod.card, Nat.card_eq_fintype_card]

private theorem s16k_card_generic_exceptional_psu_four_two :
    Nat.card (CFSG.Blueprint.Multiplier.generic .PSU 4 2 2 ×
      CFSG.Blueprint.Multiplier.exceptional .PSU 4 2 2) = 1 := by
  simp only [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional,
    CFSG.Blueprint.Multiplier.genericOrders, CFSG.Blueprint.Multiplier.exceptionalOrders,
    Nat.card_prod]
  norm_num [ZMod.card, Nat.card_eq_fintype_card]

private theorem s16k_card_generic_exceptional_psu_four_one :
    Nat.card (CFSG.Blueprint.Multiplier.generic .PSU 4 2 1 ×
      CFSG.Blueprint.Multiplier.exceptional .PSU 4 2 1) = 2 := by
  simp only [CFSG.Blueprint.Multiplier.generic, CFSG.Blueprint.Multiplier.exceptional,
    CFSG.Blueprint.Multiplier.genericOrders, CFSG.Blueprint.Multiplier.exceptionalOrders,
    Nat.card_prod]
  norm_num [ZMod.card, Nat.card_eq_fintype_card]

private theorem s16k_omegaMinus6_center_mult (hGA : CFSG.Open.GriessAllModelsStatement)
    {a : ℕ} (ha : 1 ≤ a) {X : Type} [Group X]
    [Finite X] (h : IsOmegaMinus X 6 a) :
    Subgroup.center X = ⊥ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier X ≃*
        (CFSG.Blueprint.Multiplier.generic .PSU 4 2 a ×
          CFSG.Blueprint.Multiplier.exceptional .PSU 4 2 a)) := by
  simp only [IsOmegaMinus, Nat.reduceDiv] at h
  obtain ⟨-, K, hKfield, hKfinite, b, c, hcard, hirr, ⟨e⟩⟩ := h
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := CFSG.LieType.BorelTits.charP_of_natCard_eq (p := 2) (f := a) hcard
  obtain ⟨E, hEfield, hEU, ⟨eSU⟩⟩ :=
    CFSG.ComponentClassification.RankTwoClassical.nonempty_statedOmega_quadMinus_three_equiv
      (m := a) hcard hirr
  letI : Field E := hEfield
  haveI : Finite E := hEU.finite
  haveI : CharP E 2 := hEU.charP
  have hE : Nat.card E = (2 ^ a) ^ 2 := by
    rw [hEU.card, ← pow_mul, Nat.mul_comm]
  have hnq : ((4 : ℕ), 2 ^ a) ≠ (3, 2) := fun hh =>
    absurd (congrArg Prod.fst hh) (by norm_num)
  have hSU := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (p := 2) (f := a) (n := 4) hE (by norm_num) hnq
  have hΩbot : (StatedScalars (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K).subgroupOf
      (StatedOmega (StatedQuadMinus 3 K b c)) = ⊥ := by
    refine CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
      (Q := CFSG.LieType.Universal.Spin.quadMinus 3 K b c)
      (Q₀ := StatedQuadMinus 3 K b c)
      (CFSG.LieType.Universal.Spin.coe_quadMinus 3 K b c) ?_
    refine ⟨Pi.single (Sum.inr (Sum.inr 0)) (1 : K), ?_⟩
    rw [CFSG.LieType.Universal.Spin.quadMinus_apply]
    norm_num
  have hSUbot : (StatedScalars (Fin 4) E).subgroupOf (StatedSU 4 (2 ^ a) E) = ⊥ :=
    CFSG.Quasithin.H13.F431.Un.statedScalars_inf_eq_bot (f := a) hE
  have hprojΩ : StatedProj (StatedOmega (StatedQuadMinus 3 K b c)) ≃*
      StatedOmega (StatedQuadMinus 3 K b c) :=
    (QuotientGroup.quotientMulEquivOfEq hΩbot).trans QuotientGroup.quotientBot
  have hprojSU : StatedProj (StatedSU 4 (2 ^ a) E) ≃* StatedSU 4 (2 ^ a) E :=
    (QuotientGroup.quotientMulEquivOfEq hSUbot).trans QuotientGroup.quotientBot
  have hmodeliso : X ≃* StatedProj (StatedSU 4 (2 ^ a) E) :=
    e.trans (hprojΩ.trans (eSU.trans hprojSU.symm))
  haveI : Group.IsPerfect (StatedSU 4 (2 ^ a) E) := hSU.1.1
  have hZproj : Subgroup.center (StatedProj (StatedSU 4 (2 ^ a) E)) = ⊥ :=
    s16k_center_eq_bot_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hSU.2.symm)
      (Group.IsPerfect.center_quotient_center_eq_bot (G := StatedSU 4 (2 ^ a) E))
  have hZX : Subgroup.center X = ⊥ := s16k_center_eq_bot_of_mulEquiv hmodeliso hZproj
  have hclass : StatedClassicalModel X .PSU 4 2 a :=
    ⟨⟨Nat.prime_two, ha, by norm_num, hnq⟩, E, inferInstance, hEU.finite, hE, ⟨hmodeliso⟩⟩
  have hmodel : CFSG.Models.LieModel X .PSU 4 2 a := ⟨hclass.1, Or.inl hclass⟩
  obtain ⟨-, ⟨m⟩⟩ := hGA X .PSU 4 2 a hmodel
  exact ⟨hZX, ⟨m⟩⟩

theorem s16k_trivial_sp4_four (hGA : CFSG.Open.GriessAllModelsStatement) {X : Type} [Group X]
    [Finite X] (h : IsSpn X 4 2) :
    Nat.card (Subgroup.center X) = 1 ∧ Nat.card (CFSG.Open.griessHopfMultiplier X) = 1 := by
  simp only [IsSpn, Nat.reduceDiv] at h
  obtain ⟨-, K, hKfield, hKfinite, hcard, ⟨e⟩⟩ := h
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  haveI : Fintype K := Fintype.ofFinite K
  have hK4 : Nat.card K = 4 := by rw [hcard]; norm_num
  have hbot : Subgroup.center (StatedSp 2 K) = ⊥ := s16k_center_statedSp_eq_bot hK4 2
  have hclass : StatedClassicalModel X .PSp 2 2 2 :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm
      (s16k_statedClassicalModel_statedSp (n := 2) (by norm_num) hK4)
  have hmodel : CFSG.Models.LieModel X .PSp 2 2 2 := ⟨hclass.1, Or.inl hclass⟩
  obtain ⟨-, ⟨m⟩⟩ := hGA X .PSp 2 2 2 hmodel
  refine ⟨?_, ?_⟩
  · rw [s16k_center_eq_bot_of_mulEquiv e hbot, Subgroup.card_bot]
  · rw [Nat.card_congr m.toEquiv]
    exact s16k_card_generic_exceptional_psp_two

theorem s16k_trivial_omegaMinus6_four (hGA : CFSG.Open.GriessAllModelsStatement) {X : Type}
    [Group X] [Finite X] (h : IsOmegaMinus X 6 2) :
    Nat.card (Subgroup.center X) = 1 ∧ Nat.card (CFSG.Open.griessHopfMultiplier X) = 1 := by
  obtain ⟨hZX, ⟨m⟩⟩ := s16k_omegaMinus6_center_mult hGA (a := 2) (by norm_num) h
  refine ⟨?_, ?_⟩
  · rw [hZX, Subgroup.card_bot]
  · rw [Nat.card_congr m.toEquiv]
    exact s16k_card_generic_exceptional_psu_four_two

theorem s16k_card_omegaMinus6_two (hGA : CFSG.Open.GriessAllModelsStatement) {X : Type}
    [Group X] [Finite X] (h : IsOmegaMinus X 6 1) :
    Nat.card (Subgroup.center X) = 1 ∧ Nat.card (CFSG.Open.griessHopfMultiplier X) = 2 := by
  obtain ⟨hZX, ⟨m⟩⟩ := s16k_omegaMinus6_center_mult hGA (a := 1) (by norm_num) h
  refine ⟨?_, ?_⟩
  · rw [hZX, Subgroup.card_bot]
  · rw [Nat.card_congr m.toEquiv]
    exact s16k_card_generic_exceptional_psu_four_one

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
