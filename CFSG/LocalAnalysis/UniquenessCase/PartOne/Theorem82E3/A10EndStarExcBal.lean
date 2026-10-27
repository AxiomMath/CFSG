module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndStarGamma
public import CFSG.HardMathSupport.Dickson.Bal207.Corr
import CFSG.HardMathSupport.Dickson.I271.Support.AmbAlt
import CFSG.HardMathSupport.Dickson.I271.Support.AmbU4
import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthChev
import CFSG.Adapters.CatalogueFieldBridges.Symplectic
import CFSG.LocalAnalysis.UniquenessCase.UC1K326Wreath
import CFSG.GH74.Generic.BProg.B3.S1ThreeSplit

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.GLTheoremB (IsSCp)
open CFSG.HardMathSupport.Solomon.LocalBalance (IsStronglyBalancedIn)
open CFSG.HardMathSupport.Dickson.Bal207 (Bal207Corr IsG2EightIndex)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ (Bal207Index)

private lemma pRank_top_eq_three_of_hyp327 {X : Type} [Group X] [Finite X]
    {P A : Subgroup X} (hX : UC22.InS3.UC327.Hyp327 X P A)
    (hPZ : Nonempty (↥P ≃* UC22.InS3.UC326.ZWr 1)) :
    CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hPgrp, hPidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hX.sylow
  have hPsyl : CFSG.Open.pRank 3 P = CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
    (CFSG.SectionRank.pRank_sylow
      (hPgrp.toSylow (by rwa [Subgroup.relIndex_top_right] at hPidx))).1
  obtain ⟨eZ⟩ := hPZ
  rw [← hPsyl, CFSG.SectionRank.pRank_eq_pRank_top_subgroup P]
  exact UC22.InS3.UC326.zwr_pRank (n := 1) (by norm_num) eZ

private lemma isSCp_top_of_hyp327 {X : Type} [Group X] [Finite X]
    {P A : Subgroup X} (hX : UC22.InS3.UC327.Hyp327 X P A)
    (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 3) :
    CFSG.LocalAnalysis.GLTheoremB.IsSCp 3 ⊤ A := by
  refine ⟨le_top, hX.elem, ?_⟩
  intro E _ hE hAE
  have hEcard : Nat.card E ≤ 27 := by
    obtain ⟨r, hr⟩ := hE.isPGroup.exists_card_eq
    have hle : r ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
      CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_top hE (k := r) hr
    rw [h3] at hle
    calc Nat.card E = 3 ^ r := hr
      _ ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hle
      _ = 27 := by norm_num
  exact (Subgroup.eq_of_le_of_card_ge hAE (by simpa [hX.card] using hEcard)).symm

private lemma isStronglyBalancedIn_of_isAlt_nine
    {X : Type} [Group X] [Finite X] {L A : Subgroup X}
    (hcore : CFSG.pPrimeCore 3 X = ⊥) (hq : CFSG.Open.IsQuasisimple ↥L) (hLn : L.Normal)
    (hZ : Subgroup.center ↥L = ⊥) (hAL : A ≤ L) (hAcard : Nat.card A = 27)
    (hSC : IsSCp 3 ⊤ A) (hAN : A ≤ Subgroup.normalizer (L : Set X))
    (hAlt : UC22.IsAlt ↥L 9) : IsStronglyBalancedIn 3 A L := by
  obtain ⟨e⟩ := hAlt
  have h3L : 3 ∣ Nat.card L := by
    have h3A : 3 ∣ Nat.card A := by rw [hAcard]; norm_num
    exact h3A.trans (Subgroup.card_dvd_of_le hAL)
  have hcomp : CFSG.Open.GLAPComponent 3 ⊤ L :=
    CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_normal Nat.prime_three hq h3L le_top
      (Subgroup.Normal.subgroupOf hLn ⊤)
  refine CFSG.HardMathSupport.Dickson.I271.Amb.altCore (p := 3) (K := L) (B := A) (n := 9)
    Nat.prime_three (by norm_num) ?_ hcomp hSC hAN (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ?_
  · exact hcore
  · exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e

private lemma exists_bal207Index_psu_four_two {Y : Type} [Group Y]
    (h : LieModel Y .PSU 4 2 1) :
    ∃ d : TauCeti.ValidLieTypeIndex, Bal207Index 3 d.1 ∧ ¬ IsG2EightIndex d.1 ∧
      Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  obtain ⟨q, hv, hq, he⟩ :=
    CFSG.HardMathSupport.Dickson.DefCharOuter.Export.Sporth.nonempty_equiv_twistedA_three
      (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num : (4 : ℕ) ≠ 0) h)
  obtain ⟨hq2, hqe⟩ := CFSG.HardMathSupport.Dickson.I271.Amb.u4_p_exponent hq
  exact ⟨⟨.twistedA 3 q, hv⟩, ⟨rfl, Or.inl ⟨Or.inl ⟨hq2, hqe⟩, by norm_num⟩⟩,
    fun h => h, he⟩

private lemma exists_bal207Index_psp_six_two {Y : Type} [Group Y]
    (h : LieModel Y .PSp 3 2 1) :
    ∃ d : TauCeti.ValidLieTypeIndex, Bal207Index 3 d.1 ∧ ¬ IsG2EightIndex d.1 ∧
      Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group) := by
  obtain ⟨-, K, hfield, hfinite, hK, ⟨θ⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num : (3 : ℕ) ≠ 0) h
  let _ := hfield
  let _ := hfinite
  let q : TauCeti.PrimePower := ⟨2, 1, Nat.prime_two, Nat.one_pos⟩
  have hq2 : q.card = 2 := by rw [TauCeti.PrimePower.card_def]; rfl
  have hv : (TauCeti.LieTypeIndex.B 3 q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    refine ⟨⟨by norm_num, fun h => absurd h.1 (by norm_num)⟩, fun h => ?_⟩
    have h3 : q.card = 3 := h.2
    rw [hq2] at h3
    exact absurd h3 (by norm_num)
  have hKcard : Nat.card K = q.card := by
    rw [hK, TauCeti.PrimePower.card_def]
  obtain ⟨e⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_mulEquiv_lie_B_of_statedProj
    (r := 3) hv (by rfl : q.p = 2) (by norm_num : 3 ≤ 3) hKcard
  exact ⟨⟨.B 3 q, hv⟩, ⟨rfl, Or.inl ⟨⟨rfl, rfl⟩, le_rfl⟩⟩, fun h => h, ⟨θ.trans e⟩⟩

private lemma isStronglyBalancedIn_of_bal207 {X : Type} [Group X] [Finite X]
    (hB : Bal207Corr) {L A : Subgroup X} (hKg : CFSG.Open.IsKGroup X)
    (hK : CFSG.Open.IsComponentOf L ⊤) (hSC : IsSCp 3 ⊤ A)
    (hAN : A ≤ Subgroup.normalizer (L : Set X)) (hZ : Subgroup.center ↥L = ⊥)
    {d : TauCeti.ValidLieTypeIndex} (hd : Bal207Index 3 d.1) (hg2 : ¬ IsG2EightIndex d.1)
    (e : ↥L ≃* (TauCeti.CFSGIndex.lie d).Group) : IsStronglyBalancedIn 3 A L :=
  hB X hKg 3 L A Nat.prime_three (by norm_num) hK hSC hAN d hd
    ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans e⟩
    fun h => (hg2 h).elim

theorem kFactE27SignalizerExceptional_of_bal
    (hB : CFSG.HardMathSupport.Dickson.Bal207.Bal207Corr) : KFactE27SignalizerExceptional := by
  intro X _ _ P A hKg hX hPZ hcore _hbal L hL hC hPL hExc W hW hcop
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAP : A ≤ P := hX.jA ▸ Subgroup.map_subtype_le _
  have hAL : A ≤ L := hAP.trans hPL
  have hLn : L.Normal :=
    CFSG.GH74.Generic.BProg.B3.S1Three.normal_of_centralizer_le (z := 1) hL fun w hw => by
      rw [hC] at hw
      exact Or.inl (Subgroup.mem_bot.mp hw)
  have hZ : Subgroup.center ↥L = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hz' : (z : X) ∈ (Subgroup.center ↥L).map L.subtype := ⟨z, hz, rfl⟩
    rw [CFSG.LocalCores.mem_map_center_iff] at hz'
    have hbot : (z : X) ∈ (⊥ : Subgroup X) := by rw [← hC]; exact hz'.2
    exact Subtype.ext (Subgroup.mem_bot.mp hbot)
  have hKcomp : CFSG.Open.IsComponentOf L ⊤ := (CFSG.isComponent_iff_open L).1 hL
  have hqL : CFSG.Open.IsQuasisimple ↥L := hKcomp.2.2
  have hSC : IsSCp 3 ⊤ A := isSCp_top_of_hyp327 hX (pRank_top_eq_three_of_hyp327 hX hPZ)
  have hNtop : Subgroup.normalizer (L : Set X) = ⊤ := Subgroup.normalizer_eq_top L
  have hAN : A ≤ Subgroup.normalizer (L : Set X) := by rw [hNtop]; exact le_top
  have hstr : IsStronglyBalancedIn 3 A L := by
    rcases hExc with hAlt | hPSp | hPSU | hB3
    · exact isStronglyBalancedIn_of_isAlt_nine hcore hqL hLn hZ hAL hX.card hSC hAN hAlt
    · obtain ⟨d, hd, hg2, ⟨e⟩⟩ := exists_bal207Index_psu_four_two (Y := ↥L)
        (Or.inl ⟨by decide,
          CFSG.ClassicalModels.statedClassicalModel_PSU_four_two_of_PSp_two_three
            (hPSp.statedClassicalModel (by decide))⟩)
      exact isStronglyBalancedIn_of_bal207 hB hKg hKcomp hSC hAN hZ hd hg2 e
    · obtain ⟨d, hd, hg2, ⟨e⟩⟩ := exists_bal207Index_psu_four_two (Y := ↥L) hPSU
      exact isStronglyBalancedIn_of_bal207 hB hKg hKcomp hSC hAN hZ hd hg2 e
    · obtain ⟨d, hd, hg2, ⟨e⟩⟩ := exists_bal207Index_psp_six_two (Y := ↥L) hB3
      exact isStronglyBalancedIn_of_bal207 hB hKg hKcomp hSC hAN hZ hd hg2 e
  have h := hstr W (by rw [hNtop]; exact le_top) hcop.symm
    (by rw [hNtop, inf_top_eq]; exact hW)
  rw [hC] at h
  exact le_bot_iff.mp h

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
