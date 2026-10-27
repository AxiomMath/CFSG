module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KBorelSolv20_7.Holds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeMinimal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem Ctx23L.inf_M_le_normalizer_sylow {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h2010 : S20_10 D) (h1930 : H1930 D) (hRB : KRankOneBorel) :
    c.L0 ⊓ D.M ≤ Subgroup.normalizer ((D.T ⊓ c.L0 : Subgroup G) : Set G) := by
  have hTM : D.T ≤ D.M := D.sylowM.le
  have hTJ : D.T ≤ Subgroup.normalizer ((c.L0 ⊓ D.M : Subgroup G) : Set G) :=
    (le_inf c.hL0.1.1 (hTM.trans Subgroup.le_normalizer)).trans
      (Subgroup.inf_normalizer_le_normalizer_inf)
  have hSJ : D.T ⊓ c.L0 ≤ c.L0 ⊓ D.M := by
    intro x hx
    exact ⟨hx.2, hTM hx.1⟩
  rcases hRB (T := D.T) (L := c.L0) (J := c.L0 ⊓ D.M) D.sylowG.isPGroup
    c.hL0.1.1 (isSylowIn_T_inf c) c.hL0.1.2.1 (s20_10Shape_of h2010 h1930 c.hL0) hSJ
    inf_le_left hTJ with h | h
  · exact h
  · exact absurd (h ▸ inf_le_right) (L0_not_le_M c)

theorem Ctx23L.isSolvable_inf_normalizer_sylow {D : Data G} {Ch : Choice2011 G}
    (c : Ctx23L D Ch) (h207 : S20_7 D) (h1930 : H1930 D) :
    Group.IsSolvable ↥(c.L0 ⊓ Subgroup.normalizer ((D.T ⊓ c.L0 : Subgroup G) : Set G)) := by
  let B : Subgroup G := c.L0 ⊓ Subgroup.normalizer ((D.T ⊓ c.L0 : Subgroup G) : Set G)
  change Group.IsSolvable ↥B
  have h0 : Hinf B = ⊥ := hinf_borel_eq_bot_of h207 kBorelSolv20_7_holds h1930 c.hL0.1 (isSylowIn_T_inf c)
  have h0' : CFSG.perfectResidual ↥B = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (CFSG.perfectResidual ↥B) B.subtype_injective).1
      (by simpa [B, Hinf, CFSG.inSubgroup] using h0)
  exact CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_eq_bot_iff_solvable.mp h0'

theorem Ctx23L.isSolvable_inf_M {D : Data G} {Ch : Choice2011 G} (c : Ctx23L D Ch)
    (h2010 : S20_10 D) (h207 : S20_7 D) (h1930 : H1930 D) (hRB : KRankOneBorel) :
    Group.IsSolvable ↥(c.L0 ⊓ D.M) := by
  haveI : Group.IsSolvable
      ↥(c.L0 ⊓ Subgroup.normalizer ((D.T ⊓ c.L0 : Subgroup G) : Set G)) :=
    isSolvable_inf_normalizer_sylow c h207 h1930
  have hle : c.L0 ⊓ D.M ≤
      c.L0 ⊓ Subgroup.normalizer ((D.T ⊓ c.L0 : Subgroup G) : Set G) :=
    le_inf inf_le_left (inf_M_le_normalizer_sylow c h2010 h1930 hRB)
  refine Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle) ?_
  exact Subgroup.inclusion_injective hle

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
