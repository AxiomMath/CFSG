module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatParMax.ProdFactors
public import CFSG.RankThree.GF2n.Stroth80.ClassicalQuasisimple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)

private theorem isQuasisimple_of_isSp4 {X : Type} [Group X] {n : ℕ}
    (h : IsSp4 X n) (hn : 2 ≤ n) : CFSG.Open.IsQuasisimple X := by
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  letI : Field K := hKf
  letI : Finite K := hKfin
  have h4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  haveI : CharP K 2 :=
    CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  have hbot := CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot (n := 2) (K := K)
  let eΩ : StatedProj (StatedSp 2 K) ≃* StatedSp 2 K :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  have hq := CFSG.LieType.Universal.Symplectic.isQuasisimple 2 K (by norm_num)
    (Or.inl (Or.inr h4))
  have hqX := hq.of_mulEquiv (e.trans eΩ)
  exact ⟨hqX.1.commutator_eq_top, hqX.2.1⟩

private theorem isQuasisimple_of_isSLn {X : Type} [Group X] {d a : ℕ} (hd : 2 ≤ d)
    (h : IsSLn X d a) (ha : 2 ≤ a) : CFSG.Open.IsQuasisimple X := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h
  letI : Field K := hKf
  letI : Finite K := hKfin
  have h4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have hq := CFSG.RankThree.GF2n.Stroth80.statedSL_quasisimple_of_card d K hd h4
  have hqX := hq.of_mulEquiv e
  exact ⟨hqX.1.commutator_eq_top, hqX.2.1⟩

private theorem isQuasisimple_of_isSUn_four {X : Type} [Group X] {a : ℕ}
    (h : IsSUn X 4 a) : CFSG.Open.IsQuasisimple X := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h
  letI : Field K := hKf
  letI : Finite K := hKfin
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hne : ((4 : ℕ), 2 ^ a) ≠ (3, 2) := by
    intro hpair
    exact absurd (congrArg Prod.fst hpair) (by norm_num)
  have hq := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (p := 2) (f := a) (F := K) (n := 4) hKcard (by norm_num) hne
  have hqX := hq.1.of_mulEquiv e
  exact ⟨hqX.1.commutator_eq_top, hqX.2.1⟩

private theorem isQuasisimple_of_statedProj_omegaMinus {X : Type} [Group X] {m : ℕ}
    (hm : 2 ≤ m) {K : Type} [Field K] [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : X ≃* StatedProj (StatedOmega (StatedQuadMinus m K b c))) :
    CFSG.Open.IsQuasisimple X := by
  let Q : QuadraticForm K (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) :=
    CFSG.LieType.Universal.Spin.quadMinus m K b c
  have hQ : ⇑Q = StatedQuadMinus m K b c :=
    CFSG.LieType.Universal.Spin.coe_quadMinus m K b c
  let P := CFSG.ClassicalGroups.Orthogonal.minusPair K b c (⟨0, by omega⟩ : Fin (m - 1))
  have hv : ∃ v, Q v ≠ 0 := by
    refine ⟨P.e + P.f, ?_⟩
    show CFSG.LieType.Universal.Spin.quadMinus m K b c (P.e + P.f) ≠ 0
    rw [CFSG.Timmesfeld.ClassicalOrders.map_add_eq_one_of_hypPair P]
    exact one_ne_zero
  have hbot := CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot hQ hv
  let eΩ : StatedProj (StatedOmega (StatedQuadMinus m K b c)) ≃*
      StatedOmega (StatedQuadMinus m K b c) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  have hq := CFSG.RankThree.GF2n.Stroth80.statedOmega_minus_quasisimple_of_two_le
    K (m := m) (b := b) (c := c) hm hirr
  have hqX := hq.of_mulEquiv (e.trans eΩ)
  exact ⟨hqX.1.commutator_eq_top, hqX.2.1⟩

private theorem isQuasisimple_of_isOmegaMinus {X : Type} [Group X] {n a : ℕ}
    (h : IsOmegaMinus X n a) (hm : 2 ≤ n / 2) : CFSG.Open.IsQuasisimple X := by
  obtain ⟨-, K, hKf, hKfin, b, c, hKcard, hirr, ⟨e⟩⟩ := h
  letI : Field K := hKf
  letI : Finite K := hKfin
  haveI : CharP K 2 :=
    CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  exact isQuasisimple_of_statedProj_omegaMinus hm b c hirr e

private theorem isQuasisimple_of_isOmegaPlus_six {X : Type} [Group X] {a : ℕ}
    (h : IsOmegaPlus X 6 a) : CFSG.Open.IsQuasisimple X := by
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h
  letI : Field K := hKf
  letI : Finite K := hKfin
  haveI : CharP K 2 :=
    CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  let Q : QuadraticForm K (Fin 3 ⊕ Fin 3 → K) := CFSG.LieType.Universal.Spin.quadPlus 3 K
  have hQ : ⇑Q = StatedQuadPlus 3 K :=
    CFSG.LieType.Universal.Spin.coe_quadPlus 3 K
  let P := CFSG.ClassicalGroups.Orthogonal.plusPair K (⟨0, by norm_num⟩ : Fin 3)
  have hv : ∃ v, Q v ≠ 0 := by
    refine ⟨P.e + P.f, ?_⟩
    show CFSG.LieType.Universal.Spin.quadPlus 3 K (P.e + P.f) ≠ 0
    rw [CFSG.Timmesfeld.ClassicalOrders.map_add_eq_one_of_hypPair P]
    exact one_ne_zero
  have hbot := CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot hQ hv
  let eΩ : StatedProj (StatedOmega (StatedQuadPlus 3 K)) ≃*
      StatedOmega (StatedQuadPlus 3 K) :=
    (QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot
  have hq := CFSG.RankThree.GF2n.Stroth80.statedOmega_plus_quasisimple_of_three_le
    K 3 (by norm_num)
  have hqX := hq.of_mulEquiv (e.trans eΩ)
  exact ⟨hqX.1.commutator_eq_top, hqX.2.1⟩

private theorem isQuasisimple_of_isSpn_six {X : Type} [Group X] {a : ℕ}
    (h : IsSpn X 6 a) (ha : 2 ≤ a) : CFSG.Open.IsQuasisimple X := by
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h
  letI : Field K := hKf
  letI : Finite K := hKfin
  have h4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have hq := CFSG.LieType.Universal.Symplectic.isQuasisimple 3 K (by norm_num)
    (Or.inl (Or.inr h4))
  have hqX := hq.of_mulEquiv e
  exact ⟨hqX.1.commutator_eq_top, hqX.2.1⟩

private theorem isQuasisimple_of_isOmega8m {X : Type} [Group X] {n : ℕ}
    (h : IsOmega8m X n) : CFSG.Open.IsQuasisimple X := by
  obtain ⟨-, K, hKf, hKfin, hKcard, b, c, hirr, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  letI : Field K := hKf
  letI : Finite K := hKfin
  haveI : CharP K 2 :=
    CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hKcard
  exact isQuasisimple_of_statedProj_omegaMinus (m := 4) (by norm_num) b c hirr e

theorem isQuasisimple_of_isNaturalClassicalModule_of_not_omegaPlus
    {W : Type} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)} {n : ℕ}
    (h : IsNaturalClassicalModule H n) (hn : 2 ≤ n) (hnot : ¬ IsOmegaPlus ↥H 4 n) :
    CFSG.Open.IsQuasisimple ↥H := by
  rcases h with ⟨hL2, -⟩ | ⟨hOm4, -⟩ | ⟨hOp4, -⟩ | ⟨hSp4, -⟩ | ⟨hSL3, -⟩ |
    ⟨a, -, hSU4, -⟩ | ⟨hOm6, -⟩ | ⟨hSL4, -⟩ | ⟨hOp6, -⟩ | ⟨hSp6, -⟩ | ⟨hO8, -⟩
  · exact CFSG.LocalAnalysis.UniquenessCase.UC22.NatParMax.isQuasisimple_of_isL2 hL2
  · exact isQuasisimple_of_isOmegaMinus hOm4 (by norm_num)
  · exact absurd hOp4 hnot
  · exact isQuasisimple_of_isSp4 hSp4 hn
  · exact isQuasisimple_of_isSLn (d := 3) (by norm_num) hSL3 hn
  · exact isQuasisimple_of_isSUn_four hSU4
  · exact isQuasisimple_of_isOmegaMinus hOm6 (by norm_num)
  · exact isQuasisimple_of_isSLn (d := 4) (by norm_num) hSL4 hn
  · exact isQuasisimple_of_isOmegaPlus_six hOp6
  · exact isQuasisimple_of_isSpn_six hSp6 hn
  · exact isQuasisimple_of_isOmega8m hO8

end CFSG.LocalAnalysis.UniquenessCase.UC22
