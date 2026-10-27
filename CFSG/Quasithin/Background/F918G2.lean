module

public import CFSG.Quasithin.Background.A3StructureDefs
import CFSG.RankThree.PartTwo.Census.OddClassical.SmallThree
import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineGroups
public import CFSG.Assembly.GL83LieDefs
public import CFSG.LieType.Universal.Unitary.Comparison

public section

namespace CFSG.Quasithin

section UnitaryThree

open CFSG.RankThree.PartTwo.Census CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F] [Finite F] [CharP F 3]

private theorem two_le_pRank_three_SU (hF : Nat.card F = 9) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (SU (unitaryInvolution F 3 1) 3)) := by
  obtain ⟨i, hi⟩ : IsSquare (-1 : F) := by
    have := Fintype.ofFinite F
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hF]
    decide
  have hi' : i * i = -1 := hi.symm
  have hσ : unitaryInvolution F 3 1 i = -i := by
    rw [unitaryInvolution_apply, pow_one, pow_succ, pow_two, hi', neg_one_mul]
  let Q : Subgroup (SU (unitaryInvolution F 3 1) 3) :=
    (unitriangularThree F).subgroupOf (SU (unitaryInvolution F 3 1) 3)
  have hQp : IsPGroup 3 Q := by
    intro g
    obtain ⟨k, hk⟩ := isPGroup_unitriangularThree (K := F) ⟨_, g.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hk
    simpa using this
  let x : Q := ⟨⟨suThreeX F, suThreeX_mem⟩, isUnitriThree_suThreeXMat⟩
  let y : Q := ⟨⟨suThreeY i, suThreeY_mem hi' hσ⟩, isUnitriThree_suThreeYMat i⟩
  have hnc : ¬ IsCyclic Q := by
    intro hcyc
    exact suThreeX_mul_ne hi' (congrArg (fun z : Q => z.1.1) (mul_comm' x y))
  have : Fact (IsPGroup 3 Q) := ⟨hQp⟩
  obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a (R := Q) (p := 3) (by norm_num) hnc
  exact CFSG.SectionRank.le_pRank (by norm_num) (le_top (a := S.map Q.subtype))
    (CFSG.SectionRank.isElemAbelian_map
      ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 S).mp hSel) Q.subtype)
    (by rw [Subgroup.card_map_of_injective Q.subtype_injective, hScard])

private theorem pRank_three_SU_eq (hF : Nat.card F = 9) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (SU (unitaryInvolution F 3 1) 3)) = 2 :=
  le_antisymm (pRank_three_SU_three_le hF) (two_le_pRank_three_SU hF)

private theorem pRank_three_statedProj_eq (hF : Nat.card F = 9) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSU 3 3 F))) = 2 := by
  have hF' : Nat.card F = (3 ^ 1) ^ 2 := by rw [hF]; norm_num
  obtain ⟨P, hP⟩ := exists_wittMatrix hF' 3
  have h1 : CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSU 3 3 F))) =
      CFSG.Open.pRank 3 (⊤ : Subgroup (StatedSU 3 3 F)) :=
    CFSG.SectionRank.pRank_quotient_eq _ (by
      rw [CFSG.LinearGroups.UnitaryThreeOverNine.statedScalars_subgroupOf_statedSU_eq_bot hF,
        Subgroup.card_bot]
      norm_num)
  have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup (StatedSU 3 3 F)) =
      CFSG.Open.pRank 3 (⊤ : Subgroup (SU (unitaryInvolution F 3 1) 3)) :=
    (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) ((conjEquiv P hP).trans
      (MulEquiv.subgroupCongr (SUid_eq_statedSU hF' 3)))).symm
  rw [h1, h2]
  exact pRank_three_SU_eq hF

end UnitaryThree

theorem pRank_three_psu33 {X : Type} [Group X] [Finite X] (h : IsPSU 3 3 1 X) :
    CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have hK9 : Nat.card K = 9 := by rw [hK]; norm_num
  have := Fintype.ofFinite K
  have : CharP K 3 := charP_of_card_eq_prime_pow (p := 3) (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hK9]; norm_num)
  have e' : X ≃* CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSU 3 3 K) := e
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e']
  exact pRank_three_statedProj_eq hK9

end CFSG.Quasithin
