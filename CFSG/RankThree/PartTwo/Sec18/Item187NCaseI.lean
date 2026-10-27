module

public import CFSG.RankThree.PartTwo.Sec18.Item182
public import CFSG.RankThree.PartTwo.Sec18.Item187NLayer
public import CFSG.RankThree.PartTwo.Sec18.Item187NSuz
public import CFSG.RankThree.PartTwo.Sec18.Item187NGen
public import CFSG.RankThree.PartTwo.Sec18.Item187NFacts

public section

open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly.RankThreeEven (projSL)


variable {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {c : G} {X : Subgroup G}

theorem MinCex.fixedSubgroupOf_sup_eq_top (h186 : Item186H) (hX : MinCex A M H c X)
    (hns : ¬ Group.IsSolvable ↥X) :
    fixedSubgroupOf (cAct X hX.c_mem_normalizer) ⊔
      sylowImage X (CFSG.Open.pCoreOf 2 (H ⊓ M)) = ⊤ := by
  have hl : layer (NSolY X) ≠ ⊥ :=
    layer_ne_bot_of_not_isSolvable (pCore_NSolY X) hX.not_three_dvd_Y hX.rank_Y
      (not_isSolvable_nsolY X hns)
  have hT : IsSylowOf 2 (sylowImage X (CFSG.Open.pCoreOf 2 (H ⊓ M))) ⊤ :=
    isSylowOf_sylowImage (hX.isSylowOf_S h186)
  have hY := hX.layer_sup_sylowImage_eq_top h186 hl
  have hσ := cAct_pow_three X hX.c_mem_normalizer hX.c_pow_three
  have hcomp : ∀ K : Subgroup (NSolY X), IsComponent K →
      ∃ n, CFSG.Blueprint.SuzukiModel ↥K 2 n := fun K hK =>
    suzukiModel_of_isComponent hX.isKGroup_Y hX.not_three_dvd_Y (pCore_NSolY X) hK
  have hinv : ∀ K : Subgroup (NSolY X), IsComponent K →
      K.map (cAct X hX.c_mem_normalizer).toMonoidHom = K := fun K hK =>
    isComponent_map_eq_of_suzuki hX.isKGroup_Y hX.not_three_dvd_Y (pCore_NSolY X)
      (hX.rank_Y 5 (by norm_num) (by norm_num)) _ hσ hK
  have hle := layer_le_fixedSubgroupOf_sup (cAct X hX.c_mem_normalizer) hσ hcomp hinv hT
  rw [eq_top_iff, ← hY]
  exact sup_le hle le_sup_right

theorem MinCex.false_of_pCore_ne_bot (h186 : Item186H) (hX : MinCex A M H c X)
    (hns : ¬ Group.IsSolvable ↥X)
    (hO : CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({c} : Set G)) ≠ ⊥) : False := by
  have hY := hX.fixedSubgroupOf_sup_eq_top h186 hns
  have hXle := le_sup_centralizer_of_fixedSubgroupOf_sup X (CFSG.Open.pCoreOf 2 (H ⊓ M))
    hX.c_mem_normalizer hX.c_pow_three hX.pCoreOf_le (hX.pCoreOf_le_S h186) hY
  have hzp := centralizer_singleton_le_normalizer_zpowers c
  have hCN : Subgroup.centralizer ({c} : Set G) ≤
      Subgroup.normalizer (inSubgroup perfectResidual H : Set G) :=
    hzp.trans (hX.hyp187.2.2 hO)
  have hSN : CFSG.Open.pCoreOf 2 (H ⊓ M) ≤
      Subgroup.normalizer (inSubgroup perfectResidual H : Set G) :=
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 (H ⊓ M)).trans inf_le_left).trans
      (CFSG.RankThree.PartTwo.Sec18.le_normalizer_inSubgroup_perfectResidual H)
  exact hX.not_le (hXle.trans (sup_le (inf_le_right.trans hCN) hSN))

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
