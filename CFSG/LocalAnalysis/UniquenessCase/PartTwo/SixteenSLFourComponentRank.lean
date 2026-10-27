module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSimpleComponentRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenCfg2Simple
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumConv
public import CFSG.Quasithin.Background.A3FactsClassical
public import CFSG.Quasithin.Vol2.Ch7Sec77Mult
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s15_eq_one_of_sl_four_component_at_three
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hSL4 : IsSLn ↥(lBar V₀ V hV L) 4 1) :
    s15 D.M V₀ V hV L = 1 := by
  have hLn4 : IsLn ↥(lBar V₀ V hV L) 4 1 := s16k_isLn_of_isSLn (by norm_num) hSL4
  have hsimple : IsSimpleGroup ↥(lBar V₀ V hV L) := s16c167_cfg2_simple_ln hLn4
  have hclass : StatedClassicalModel ↥(lBar V₀ V hV L) .PSL 4 2 1 :=
    (CFSG.Blueprint.LieModel.classical_iff (t := .PSL) (n := 4) (p := 2) (f := 1)
      (by decide)).mp hLn4
  have hclass' := hclass
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hclass'
  have hrank : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(lBar V₀ V hV L)) :=
    calc 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (StatedProj (StatedSL 4 K))) :=
          CFSG.Quasithin.A3Facts.psl_two_le_pRank_three (K := K) (n := 4) (by norm_num)
      _ = CFSG.Open.pRank 3 (⊤ : Subgroup ↥(lBar V₀ V hV L)) :=
          (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e).symm
  have hcover : ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q →
      Nonempty ((Q ⧸ Subgroup.center Q) ≃* ↥(lBar V₀ V hV L)) →
      IsPGroup 2 ↥(Subgroup.center Q) := by
    intro Q _ _ hQ ⟨eQ⟩
    have hperf : Group.IsPerfect Q := Group.isPerfect_def.mpr hQ.1
    obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.GriessClassical.psl_row
      (X := ↥(lBar V₀ V hV L)) hclass
    have hdvdM : Nat.card (CFSG.Open.griessHopfMultiplier ↥(lBar V₀ V hV L)) ∣ 2 := by
      rw [Nat.card_congr eM.toEquiv]
      exact CFSG.Quasithin.H13.SLMult.card_table_dvd_two (m := 4) (Or.inr (Or.inl rfl))
    have hdvd := (CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier
      (Q := Q) (S := ↥(lBar V₀ V hV L)) hperf eQ).trans hdvdM
    exact IsPGroup.of_card_dvd_pow (n := 1) (by simpa using hdvd)
  exact s15_eq_one_of_simple_component_of_three_rank c hcomp hsimple (r := 2) (by norm_num)
    hrank hcover

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
