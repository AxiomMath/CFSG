module

import CFSG.LocalAnalysis.StandardType.GGTriD4ComponentsPGLDer
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.Assembly.GL83StatedBridge
import CFSG.LocalAnalysis.OddStandard.GH71.S55Comp5SU
import CFSG.RankThree.GF2n.Stroth80.GriessOrthSmall
import CFSG.Models.Blueprint
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
open CFSG.RankThree.PartTwo
open CFSG.RankThree.Classical2 (unitarySet)

private theorem r891_quotient_center_statedSL {L : Type} [Group L] {F : Type} [Field F]
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 3) F) :
    Nonempty (L ⧸ Subgroup.center L ≃* StatedProj (StatedSL 3 F)) := by
  let eS : Matrix.SpecialLinearGroup (Fin 3) F ⧸
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) ≃* StatedProj (StatedSL 3 F) :=
    QuotientGroup.congr _ _ (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F)
      (CFSG.Assembly.LowTwoRank.map_center_eq_statedScalars 3 F)
  exact ⟨(QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).trans eS⟩

theorem threeCover_psl3_of_mulEquiv {L : Type} [Group L] {n : ℕ} (hn : 2 ≤ n) (hev : Even n)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ n) (hq : CFSG.IsQuasisimple L)
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 3) F) :
    ThreeCover (fun Y _ => LieModel Y .PSL 3 2 n) L := by
  have h3 : 3 ∣ Nat.card F - 1 := by
    rw [hF]
    obtain ⟨k, rfl⟩ := hev
    have h := Nat.sub_dvd_pow_sub_pow 4 1 k
    rwa [one_pow, show (4 : ℕ) ^ k = 2 ^ (k + k) by rw [← two_mul, pow_mul]; norm_num] at h
  have hcardSL : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) = 3 := by
    rw [Nat.card_congr (Subgroup.centerCongr
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F)).toEquiv]
    exact CFSG.Open.StatedCenterThree.card_center_statedSL_three h3
  refine ⟨⟨hq.1.commutator_eq_top, hq.2.1⟩, ?_, ?_⟩
  · rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, hcardSL]
  · obtain ⟨eQ⟩ := r891_quotient_center_statedSL e
    exact LieModel.of_mulEquiv eQ.symm
      (CFSG.Models.LieModel.toBlueprint (by decide)
        (CFSG.RankThree.GF2n.Stroth80.lieModel_statedProj_sl (m := 3) (f := n)
          (by norm_num) hn hF))

theorem threeCover_psu3_of_mulEquiv {L : Type} [Group L] {n : ℕ} (hn : 2 ≤ n) (hodd : Odd n)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2] {U : Subgroup (GL (Fin 3) Ω)}
    (hU : (U : Set (GL (Fin 3) Ω)) = unitarySet (2 ^ n) 3) (hq : CFSG.IsQuasisimple L)
    (e : L ≃* ↥U) : ThreeCover (fun Y _ => LieModel Y .PSU 3 2 n) L := by
  obtain ⟨F, hField, hFin, hcard, ⟨eSU⟩⟩ :=
    CFSG.OddStandard.GH71.S55.nonempty_statedSU_mulEquiv (Ω := Ω) (ℓ := 2) (f := n)
      (by omega) hU
  let := hField
  let := hFin
  have hUF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n F := by
    refine ⟨Nat.prime_two, by omega, ?_⟩
    rw [hcard, ← pow_mul, Nat.mul_comm]
  have hq2 : 2 < 2 ^ n :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
  have h3 : 3 ∣ 2 ^ n + 1 := by
    have := Odd.nat_add_dvd_pow_add_pow 2 1 hodd
    simpa using this
  have hcardSU : Nat.card (Subgroup.center ↥(StatedSU 3 (2 ^ n) F)) = 3 :=
    CFSG.Open.StatedCenterThree.card_center_statedSU_three hcard h3
  have hZeq : Subgroup.center (StatedSU 3 (2 ^ n) F) =
      (StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (2 ^ n) F) :=
    (CFSG.RankThree.PartTwo.KFacts.center_unitarySU_three (h := hUF) hq2).trans
      (CFSG.ClassicalGroups.UnitaryFlag.unitaryScalars_eq hUF (by norm_num))
  let eL : L ≃* StatedSU 3 (2 ^ n) F := e.trans eSU.symm
  have hne : (3, 2 ^ n) ≠ (3, 2) := by
    intro h
    have h2 : 2 ^ n = 2 := (Prod.mk.inj h).2
    have hlt := Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega : 1 < n)
    rw [h2] at hlt
    norm_num at hlt
  let eQ : L ⧸ Subgroup.center L ≃* StatedProj (StatedSU 3 (2 ^ n) F) :=
    (QuotientGroup.congr _ _ eL (Subgroup.map_center_eq eL)).trans
      (QuotientGroup.quotientMulEquivOfEq hZeq)
  refine ⟨⟨hq.1.commutator_eq_top, hq.2.1⟩, ?_, ?_⟩
  · rw [Nat.card_congr (Subgroup.centerCongr eL).toEquiv, hcardSU]
  · exact LieModel.of_mulEquiv eQ.symm
      (CFSG.Models.LieModel.toBlueprint (by decide)
        (CFSG.RankThree.GF2n.Stroth80.lieModel_statedProj_su (n := 3) (f := n)
          (by norm_num) hne (by omega) hcard))

theorem exists_mulEquiv_statedSU_two {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharP Ω 2]
    {U : Subgroup (GL (Fin 3) Ω)} (hU : (U : Set (GL (Fin 3) Ω)) = unitarySet (2 ^ 1) 3) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (↥U ≃* ↥(StatedSU 3 2 F)) := by
  obtain ⟨F, hField, hFin, hcard, ⟨e⟩⟩ :=
    CFSG.OddStandard.GH71.S55.nonempty_statedSU_mulEquiv (Ω := Ω) (ℓ := 2) (f := 1)
      (by norm_num) hU
  exact ⟨F, hField, hFin, by simpa using hcard, ⟨e.symm⟩⟩

theorem r891L3Pi_commutator_projImage {n : ℕ} (hn : 2 ≤ n) {π : Bool} {F : Type} [Field F]
    [Finite F]
    (hPi : Sec4.PiField π 2 n F) (hc : cond π (Even n) (Odd n)) :
    ⁅⁅CFSG.PGLModel.projImage (Sec4.glPi π 3 (2 ^ n) F),
          CFSG.PGLModel.projImage (Sec4.glPi π 3 (2 ^ n) F)⁆,
        ⁅CFSG.PGLModel.projImage (Sec4.glPi π 3 (2 ^ n) F),
          CFSG.PGLModel.projImage (Sec4.glPi π 3 (2 ^ n) F)⁆⁆ =
      ⁅CFSG.PGLModel.projImage (Sec4.glPi π 3 (2 ^ n) F),
        CFSG.PGLModel.projImage (Sec4.glPi π 3 (2 ^ n) F)⁆ ∧
    R891L3Pi ↥⁅CFSG.PGLModel.projImage (Sec4.glPi π 3 (2 ^ n) F),
      CFSG.PGLModel.projImage (Sec4.glPi π 3 (2 ^ n) F)⁆ n := by
  have hq2 : 2 < 2 ^ n :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn)
  cases π
  · have hodd : Odd n := by simpa using hc
    have hPi' : Sec4.PiField false 2 n F := hPi
    have hcomm : ⁅CFSG.PGLModel.projImage (Sec4.glPi false 3 (2 ^ n) F),
        CFSG.PGLModel.projImage (Sec4.glPi false 3 (2 ^ n) F)⁆ =
        CFSG.PGLModel.projImage (Sec4.slPi false 3 (2 ^ n) F) := by
      unfold CFSG.PGLModel.projImage
      rw [← Subgroup.map_commutator, CFSG.RankThree.PartTwo.Sec13.commutator_glPi hPi' hq2]
    have hperf : Group.IsPerfect ↥(CFSG.PGLModel.projImage (Sec4.slPi false 3 (2 ^ n) F)) :=
      CFSG.RankThree.PartTwo.Sec13.isPerfect_projImage_slPi hPi' hq2
    have hF' : Nat.card F = (2 ^ n) ^ 2 := hPi.card
    constructor
    · rw [hcomm, ← Subgroup.map_subtype_commutator, Group.IsPerfect.commutator_eq_top,
        Subgroup.map_top, Subgroup.range_subtype]
    · obtain ⟨eD⟩ := CFSG.StandardType.ggTriD4_pgu_derived_equiv hn hF'
      have hne : (3, 2 ^ n) ≠ (3, 2) := by
        intro h
        have h2 : 2 ^ n = 2 := (Prod.mk.inj h).2
        have hlt := Nat.pow_lt_pow_right (by norm_num : 1 < 2) (by omega : 1 < n)
        rw [h2] at hlt
        norm_num at hlt
      have hLM : LieModel (CFSG.Assembly.LargeEvenProj
          (CFSG.Assembly.LargeEvenSUGroup (Fin 3) F (2 ^ n))) .PSU 3 2 n :=
        CFSG.Models.LieModel.toBlueprint (by decide)
          (CFSG.RankThree.GF2n.Stroth80.lieModel_statedProj_su (n := 3) (f := n)
            (by norm_num) hne (by omega) hF')
      exact Or.inr ⟨hodd, LieModel.of_mulEquiv eD.symm hLM⟩
  · have hev : Even n := by simpa using hc
    have hPi' : Sec4.PiField true 2 n F := hPi
    have hcomm : ⁅CFSG.PGLModel.projImage (Sec4.glPi true 3 (2 ^ n) F),
        CFSG.PGLModel.projImage (Sec4.glPi true 3 (2 ^ n) F)⁆ =
        CFSG.PGLModel.projImage (Sec4.slPi true 3 (2 ^ n) F) := by
      unfold CFSG.PGLModel.projImage
      rw [← Subgroup.map_commutator, CFSG.RankThree.PartTwo.Sec13.commutator_glPi hPi' hq2]
    have hperf : Group.IsPerfect ↥(CFSG.PGLModel.projImage (Sec4.slPi true 3 (2 ^ n) F)) :=
      CFSG.RankThree.PartTwo.Sec13.isPerfect_projImage_slPi hPi' hq2
    have hF' : Nat.card F = 2 ^ n := hPi.card
    constructor
    · rw [hcomm, ← Subgroup.map_subtype_commutator, Group.IsPerfect.commutator_eq_top,
        Subgroup.map_top, Subgroup.range_subtype]
    · obtain ⟨eD⟩ := CFSG.StandardType.ggTriD4_pgl_derived_equiv hn hF'
      have hE : Nonempty (CFSG.Assembly.LargeEvenProj
          (CFSG.Assembly.LargeEvenSLGroup (Fin 3) F) ≃*
          StatedProj (StatedSL 3 F)) :=
        ⟨by rw [CFSG.Assembly.largeEvenSLGroup_eq_statedSL (K := F)]⟩
      obtain ⟨eP⟩ := hE
      exact Or.inl ⟨hev, LieModel.of_mulEquiv (eP.symm.trans eD.symm)
        (CFSG.Models.LieModel.toBlueprint (by decide)
          (CFSG.RankThree.GF2n.Stroth80.lieModel_statedProj_sl (m := 3) (f := n)
            (by norm_num) hn hF'))⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
