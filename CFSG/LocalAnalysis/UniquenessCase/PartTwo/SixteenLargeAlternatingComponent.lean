module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ExceptionalComponentCover
import CFSG.LocalAnalysis.OddStandard.GlueAlt
import CFSG.RankThree.PartTwo.Sec19.Item19Res3ProofCensus194
public import CFSG.Quasithin.EmptyFaithful.R3cBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s168e3_false_of_alternating_component_ge_twelve
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    {n : ℕ} (hn : 12 ≤ n)
    (hA : UC22.IsAlt ↥(lBar V₀ V hV L) n) : False := by
  classical
  obtain ⟨eA⟩ := hA
  have hsimple : IsSimpleGroup ↥(lBar V₀ V hV L) :=
    (MulEquiv.isSimpleGroup_congr eA).mpr
      (alternatingGroup.isSimpleGroup (by
        rw [Nat.card_eq_fintype_card, Fintype.card_fin]
        omega))
  obtain ⟨K, hK, -, ⟨eK⟩⟩ :=
    exists_calC_cover_of_simple_component c.setting.hyp16.hyp125 c.std.h127 c.std.h119 hcomp
      hsimple
  have hperf : Group.IsPerfect (Bar2 K) := Group.isPerfect_def.mpr hK.2.2.1
  have hZle : Nat.card (Subgroup.center (Bar2 K)) ≤ 2 :=
    @CFSG.OddStandard.GlueAlt.card_center_le_two_of_alt (Bar2 K) _ _ hperf n (by omega)
      (eK.trans eA)
  have hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center (Bar2 K)) := by
    intro h3
    have hle3 : 3 ≤ Nat.card (Subgroup.center (Bar2 K)) := Nat.le_of_dvd Nat.card_pos h3
    omega
  have h4A : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(alternatingGroup (Fin n))) :=
    CFSG.RankThree.PartTwo.Sec19.Item19Res3Proof.four_le_pRank_alternatingGroup hn
  have h4K : 4 ≤ CFSG.Open.pRank 3 K := by
    calc
      4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(alternatingGroup (Fin n))) := h4A
      _ = CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 K ⧸ Subgroup.center (Bar2 K))) :=
        (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num)
          (eK.trans eA)).symm
      _ = CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 K)) :=
        CFSG.SectionRank.pRank_quotient_eq (p := 3) (hp := ⟨Nat.prime_three⟩)
          (Subgroup.center (Bar2 K)) hZ3
      _ = CFSG.Open.pRank 3 K :=
        (CFSG.Quasithin.R3c.pRank_three_eq_pCore_quotient K).symm
  have h4M : 4 ≤ CFSG.Open.pRank 3 D.M :=
    h4K.trans
      (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) (CFSG.Open.IsSubnormal.le hK.1))
  have hle : CFSG.Open.pRank 3 D.M ≤ CFSG.Open.evenRank G :=
    CFSG.RankThreeCoreUniqueness.Helpers.local_pRank_le_evenRank 3 Nat.prime_three
      (by norm_num) D.M D.maxLocal.1
  have h3 : CFSG.Open.evenRank G = 3 := c.std.h3
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
