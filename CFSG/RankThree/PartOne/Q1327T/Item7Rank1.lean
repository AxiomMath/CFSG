module

public import CFSG.RankThree.PartOne.Q1327T.Item7Basic
public import CFSG.RankThree.PartOne.N143.Inspect613Even
public import CFSG.RankThree.PartOne.KFR4.At
public import CFSG.RankThree.PartOne.CTP.SeitzExcModels
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorCyclic

public section

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K133
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

theorem row8U3At_leaf7_zero : Row8U3At (K133.leaf7 0) := by
  intro Q _ _ p g Ē hX h
  exfalso
  obtain ⟨q, hq2, hv, ⟨e0⟩⟩ := hX
  have hp := h.prime
  have hp2 : p ≠ 2 := by have := h.five_le; omega
  obtain ⟨A, hAel, hAcard⟩ := h.exists_image
  have hmod := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A (r := 1) hv e0
  rw [hq2] at hmod
  obtain ⟨-, F, _, _, _, -, ⟨e⟩⟩ := S15K.exists_mulEquiv_sl2_of_model hmod
  have hrk := KFR4.pRank_le_one_of_equiv_sl2 hp hp2 e
  have h2 := CFSG.LieType.SteinbergBR.le_pRank_of_card hp.one_lt A hAel hAcard
  omega

theorem row8U3At_leaf7_one :
    Row8U3At (K133.leaf7 1) := by
  intro Q _ _ p g Ē hX h
  exfalso
  obtain ⟨m, hiso⟩ := hX
  have hp := h.prime
  have hp2 : p ≠ 2 := by have := h.five_le; omega
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨A, hAel, hAcard⟩ := h.exists_image
  have hmodel := CTP.suzukiModel_of_isoLie m hiso
  obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨e⟩⟩ := hmodel
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [hF, hfa]
  have e' : (Q ⧸ Subgroup.center Q) ≃* CFSG.Open.GLASzGroup a F :=
    e.trans (MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a F))
  have hsyl := CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.suzuki_model_oddSylow_cyclic
    a ha hF' e'
  have hodd : Odd (Nat.card A) := by
    rw [hAcard]
    exact (hp.eq_two_or_odd'.resolve_left hp2).pow
  have hc : IsCyclic A :=
    CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.odd_commutative_subgroup_cyclic A hodd
      hAel.toIsMulCommutative hsyl
  have hle := card_le_of_isCyclic_elemAb hp A hAel
  have : p < p ^ 2 := by
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
  omega

end CFSG.RankThree.PartOne.Q1327T
