module

public import CFSG.RankThree.GF2n.Tim79aSec23Inv
public import CFSG.ClassicalGroups.Linear.CentreInvariant
public import CFSG.ClassicalGroups.Linear.CentreGroupsDual
public import CFSG.Models.PGLSimple

public section

namespace CFSG.RankThree.GF2n.Tim79a

open Matrix CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.GroupTheory
open CFSG.ClassicalGroups.Linear.Model

variable {G : Type} [Group G] {M V Q P H : Subgroup G} [Finite G]

namespace MinCex

variable (hc : MinCex M V Q P H)
include hc

theorem false_of_linear_centre
    (hsimple : IsSimpleGroup (Xbar V H ⧸ Subgroup.center (Xbar V H))) (hd : Sec23Data V H)
    {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2]
    (e : Xbar V H ⧸ Subgroup.center (Xbar V H) ≃* StatedProj (StatedSL n K))
    {c : Fin n → K} (hc0 : c ≠ 0)
    (hV : (Vtilde V H).map e.toMonoidHom = cg n K c) : False := by
  obtain ⟨x, Λ, hnp, hxΛ, hΛ, hinv⟩ := exists_inv_data_centre n K hn hc0
  rw [← hV] at hnp hxΛ hinv
  obtain ⟨xA, ΛA, h1, h2, h3, h4⟩ := transfer_inv_data e (Vtilde V H) x Λ hnp hxΛ hΛ hinv
  exact hc.false_of_invariant hsimple hd xA ΛA h1 h2 h3 h4

theorem false_of_linear (hd : Sec23Data V H)
    {n : ℕ} (hn : 3 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2]
    (e : Xbar V H ⧸ Subgroup.center (Xbar V H) ≃* StatedProj (StatedSL n K))
    (hV : (∃ c : Fin n → K, c ≠ 0 ∧
        (Vtilde V H).map e.toMonoidHom = transvImage n K (transvCenter n K c)) ∨
      (∃ a : Fin n → K, a ≠ 0 ∧
        (Vtilde V H).map e.toMonoidHom = transvImage n K (transvAxis n K a))) : False := by
  haveI : IsSimpleGroup (StatedProj (StatedSL n K)) :=
    CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL K (by omega) (Or.inl (by omega))
      (Or.inl (by omega))
  have hsimple : IsSimpleGroup (Xbar V H ⧸ Subgroup.center (Xbar V H)) := e.isSimpleGroup
  rcases hV with ⟨c, hc0, hVc⟩ | ⟨a, ha0, hVa⟩
  · exact hc.false_of_linear_centre hsimple hd hn e hc0 hVc
  · obtain ⟨δ, hδ⟩ := exists_dualEquiv n K
    refine hc.false_of_linear_centre hsimple hd hn (e.trans δ) ha0 ?_
    rw [← hδ a, ← hVa, Subgroup.map_map]
    rfl

end MinCex

end CFSG.RankThree.GF2n.Tim79a
