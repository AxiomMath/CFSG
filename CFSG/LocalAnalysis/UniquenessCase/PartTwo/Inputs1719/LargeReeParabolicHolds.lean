module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ExceptionalParabolicsGen
public import CFSG.Quasithin.EmptyFaithful.S151CLG2F4Label
public import CFSG.Quasithin.EmptyFaithful.R3c3Lie
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogLargeReeModel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ExceptionalParabolics

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.Quasithin
open CFSG.QuasithinUnique (IsSylowTwoOf)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Bar2 IsSz IsL2)

theorem k_2F4ParabolicGen_holds :
    K_2F4ParabolicGen := by
  intro X _ _ n h2F4 S hS
  obtain ⟨a, K, hKF, hKFin, hcp, ha, hfa, hK, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_largeRee_model h2F4
  subst hfa
  obtain ⟨P, hP, hSL, hSz⟩ := CFSG.Quasithin.CLG2.rankTwoParG_f4_labelled h2F4 hS
  obtain ⟨hSzY, -⟩ := CFSG.Quasithin.CLG2.LeviDataSz.lieModel_quotient hSz
  obtain ⟨hL2Y, -⟩ := CFSG.Quasithin.CLG2.LeviDataSL.lieModel_quotient hSL (by omega) ⟨a, rfl⟩
  have hns : ∀ j, ¬ Group.IsSolvable ↥(perfectCore (P j)) := fun j =>
    CFSG.Quasithin.CLG2.not_isSolvable_perfectCore_of_levi (hP.levi j)
  refine ⟨perfectCore (P 1), perfectCore (P 0), perfectCore_perfect (P 1),
    perfectCore_perfect (P 0), hSzY, hL2Y, ?_, ?_⟩
  · rw [sup_comm (perfectCore (P 1)) (perfectCore (P 0))]
    exact CFSG.Quasithin.CLG2.sup_perfectCore_eq_top_of_res hP.res hns
  · intro α hα
    refine ⟨?_, ?_⟩
    · rw [map_perfectCore α.toMonoidHom (P 1), hP.inv α hα 1]
    · rw [map_perfectCore α.toMonoidHom (P 0), hP.inv α hα 0]

open CFSG.ComponentClassification.UnbalancedCatalog in
theorem k_2F4Parabolic_holds :
    K_2F4Parabolic := by
  intro X _ _ n h2F4 _ _
  obtain ⟨a, K, hKF, hKFin, hcp, ha, hfa, hK, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_largeRee_model h2F4
  subst hfa
  have houter : Nat.card (Outer X) = 2 * a + 1 :=
    (large_Ree_model_field_outer_group_and_inner_involutions X 2 (2 * a + 1) h2F4).2.2.2.2.1
  refine ⟨⟨CFSG.Quasithin.R3c3.two_le_pRank_three_is2F4 h2F4, houter⟩, ?_⟩
  intro S hS
  obtain ⟨P, hP, hSL, hSz⟩ := CFSG.Quasithin.CLG2.rankTwoParG_f4_labelled h2F4 hS
  obtain ⟨hSzY, hSzO⟩ := CFSG.Quasithin.CLG2.LeviDataSz.lieModel_quotient hSz
  obtain ⟨hL2Y, hL2O⟩ :=
    CFSG.Quasithin.CLG2.LeviDataSL.lieModel_quotient hSL (by omega) ⟨a, rfl⟩
  have hSle : ∀ j, S ≤ P j := hP.res.2.1
  have hlt : ∀ j, P j < ⊤ := fun j =>
    ((hP.res.2.2.1 (P j) (hSle j)).2 ⟨j, rfl⟩).lt
  have hnorm : ∀ j, S ≤ Subgroup.normalizer (perfectCore (P j) : Set X) := fun j =>
    (hSle j).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (perfectCore_le (P j))).1
        (perfectCore_normal (P j)))
  exact ⟨P 1, P 0, hSle 1, hSle 0, hlt 1, hlt 0, hP.res.1.symm,
    ⟨perfectCore (P 1), perfectCore_le (P 1), perfectCore_normal (P 1), hSzY, hSzO, hnorm 1⟩,
    ⟨perfectCore (P 0), perfectCore_le (P 0), perfectCore_normal (P 0), hL2Y, hL2O, hnorm 0⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
