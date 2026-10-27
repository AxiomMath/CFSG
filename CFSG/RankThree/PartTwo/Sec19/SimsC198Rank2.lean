module

public import CFSG.RankThree.PartTwo.Sec19.SimsC198Defs
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Psu
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Sp
public import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Omega
public import CFSG.Models.PGL
public import CFSG.RankThree.PartTwo.Sec4.Census.WiringInputs
public import CFSG.RankThree.PartTwo.KFacts.KS44Multiplier

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsC198

open CFSG
open CFSG.PGLModel (projSU projSp projOmegaPlus)
open CFSG.Assembly.RankThreeEven (f4TwoIndex)

variable {X : Type} [Group X] [Finite X]

private theorem census194RankHyp (h : RankHyp X) : Census194RankHyp X :=
  ⟨h.quasisimple, h.pCore_two, h.rank_prime, h.rank_three⟩

section Census


theorem false_of_rankHyp_PSU4_two (h : RankHyp X) {n : ℕ} (hn : 1 ≤ n) (h1 : n ≠ 1) (h3 : n ≠ 3)
    (e : X ⧸ Subgroup.center X ≃* projSU 4 2 n) : False := by
  have hadm : CFSG.Open.StatedLieAdmissible .PSU 4 2 n :=
    ⟨Nat.prime_two, hn, by norm_num, by simp⟩
  have hm := CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU hadm e
  have := Census194.RonanC194.survPSU_holds X 4 n (census194RankHyp h) hm le_rfl
  omega

theorem false_of_rankHyp_PSU5_two (h : RankHyp X) {f : ℕ} (hf : 1 ≤ f)
    (e : X ⧸ Subgroup.center X ≃* projSU 5 2 f) : False := by
  have hadm : CFSG.Open.StatedLieAdmissible .PSU 5 2 f :=
    ⟨Nat.prime_two, hf, by norm_num, by simp⟩
  have hm := CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU hadm e
  have := Census194.RonanC194.survPSU_holds X 5 f (census194RankHyp h) hm (by norm_num)
  omega

theorem false_of_rankHyp_PSU6_two (h : RankHyp X)
    (e : X ⧸ Subgroup.center X ≃* projSU 6 2 1) : False := by
  have hadm : CFSG.Open.StatedLieAdmissible .PSU 6 2 1 :=
    ⟨Nat.prime_two, le_rfl, by norm_num, by simp⟩
  have hm := CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU hadm e
  have := Census194.RonanC194.survPSU_holds X 6 1 (census194RankHyp h) hm (by norm_num)
  omega

theorem false_of_rankHyp_Sp8_two (h : RankHyp X)
    (e : X ⧸ Subgroup.center X ≃* projSp 4 (GaloisField 2 1)) : False := by
  have hadm : CFSG.Open.StatedLieAdmissible .PSp 4 2 1 :=
    ⟨Nat.prime_two, le_rfl, by norm_num, by simp⟩
  have hm := CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSp hadm e
  have := Census194.RonanC194.survPSp_holds X 4 1 (census194RankHyp h) hm (by norm_num)
  omega

theorem false_of_rankHyp_Sp6_four (h : RankHyp X)
    (e : X ⧸ Subgroup.center X ≃* projSp 3 (GaloisField 2 2)) : False := by
  have hadm : CFSG.Open.StatedLieAdmissible .PSp 3 2 2 :=
    ⟨Nat.prime_two, by norm_num, by norm_num, by simp⟩
  have hm := CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSp hadm e
  have := Census194.RonanC194.survPSp_holds X 3 2 (census194RankHyp h) hm le_rfl
  omega

theorem false_of_rankHyp_OmegaPlus_two (h : RankHyp X)
    (e : X ⧸ Subgroup.center X ≃* projOmegaPlus 4 (GaloisField 2 1)) : False := by
  have hadm : CFSG.Open.StatedLieAdmissible .POmegaPlus 4 2 1 :=
    ⟨Nat.prime_two, le_rfl, le_rfl⟩
  have hm := CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projOmegaPlus hadm e
  exact Census194.RonanC194.survPOmegaPlus_holds X 4 1 (census194RankHyp h) hm

end Census

section F4


theorem card_center_dvd_two_of_f4 (hX : IsQuasisimple X)
    (e : X ⧸ Subgroup.center X ≃* (TauCeti.CFSGIndex.lie f4TwoIndex).Group) :
    Nat.card (Subgroup.center X) ∣ 2 := by
  have hmodel : CFSG.Models.LieModel (X ⧸ Subgroup.center X) .F4 0 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, rfl⟩, Or.inr ⟨rfl, f4TwoIndex, ⟨rfl, rfl⟩, ⟨e⟩⟩⟩
  obtain ⟨⟨eM⟩, -, -⟩ := CFSG.Milestones.cl_lit_griess_schur_multipliers_central_covers_z2
    (X ⧸ Subgroup.center X) .F4 0 2 1 hmodel (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩))
  have h1 := CFSG.RankThree.PartTwo.KFacts.KS44.card_center_dvd_card_hopfMultiplier hX
  rwa [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv,
    Nat.card_congr eM.toEquiv, Nat.card_congr (Multiplicative.toAdd : _ ≃ _),
    Nat.card_zmod] at h1

theorem false_of_rankHyp_F4_two (h : RankHyp X)
    (e : X ⧸ Subgroup.center X ≃* (TauCeti.CFSGIndex.lie f4TwoIndex).Group) : False := by
  haveI : Finite (TauCeti.CFSGIndex.lie f4TwoIndex).Group := Finite.of_equiv _ e.toEquiv
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : ¬ 3 ∣ Nat.card (Subgroup.center X) := fun hd =>
    absurd (hd.trans (card_center_dvd_two_of_f4 h.quasisimple e)) (by norm_num)
  have hrank : 3 < CFSG.Open.pRank 3 (⊤ : Subgroup (X ⧸ Subgroup.center X)) := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e,
      ← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact CFSG.RankThree.PartTwo.Sec4.Census.three_lt_pRank_f4Two
  rw [CFSG.SectionRank.pRank_quotient_eq _ h3] at hrank
  exact absurd h.rank_three (not_le.2 hrank)

end F4

end CFSG.RankThree.PartTwo.Sec19.SimsC198
