module

public import CFSG.RankThree.PartTwo.Sec15.Ronan154BigDefs
public import CFSG.RankThree.PartTwo.Sec15.Item15Res6ProofExcl
public import CFSG.RankThree.PartTwo.Sec15.Item15Res3Proof159Odd
public import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofUse
import CFSG.RankThree.PartTwo.Sec15.Item152StepsExcl
import CFSG.RankThree.PartTwo.Sec15.Item15Res3Proof159W
import CFSG.RankThree.PartTwo.Sec14.Item147
public import CFSG.RankThree.PartTwo.Sec15.Item158Res2Proof159Y0

public section

namespace CFSG.RankThree.PartTwo.Sec15.Ronan154Big

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open Y4Core

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_scriptY0_of_at (hRead : Y4CoreReadR) {A L : Subgroup G} {c : G}
    (hMem : Y4CoreMemAt A) (h : Sec15R G A c L) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    {M : Subgroup G} (hM : M ∈ scriptY2 A) (hF : generalizedFitting ↥M = CFSG.pCore 2 ↥M) :
    (∃ J₁ J₂ : Subgroup G, ∀ J ∈ comp3In (delta A (lB A) M), J = J₁ ∨ J = J₂) ∧
      (∀ J ∈ comp3In (delta A (lB A) M), A ≤ Subgroup.normalizer (J : Set G) ∧
        J ∈ scriptY0 A (lB A)) ∧
      oPrimeResidualOf 3 (delta A (lB A) M) ≤ sSup (comp3In (delta A (lB A) M)) ∧
      deltaZero A (lB A) (delta A (lB A) M) ≤
        sSup (comp3In (delta A (lB A) M)) ⊔ pPrimeCoreOf 3 (delta A (lB A) M) := by
  set Z := delta A (lB A) M with hZ
  have hZY : Z ∈ scriptY A := delta_mem_scriptY hM.1
  have hZΔ : Z = delta A (lB A) Z := (delta_delta M).symm
  obtain ⟨⟨J₁, J₂, hS⟩, hD⟩ := hRead G A c L h Z hZY hZΔ
  have hA : ∀ J ∈ comp3In Z, A ≤ Subgroup.normalizer (J : Set G) := fun J hJ =>
    le_normalizer_of_isElemAbelian hS h.isElemAbelian hZY.2 hJ
  refine ⟨⟨J₁, J₂, hS⟩, fun J hJ => ⟨hA J hJ, hMem M hM hF J hJ (hA J hJ)⟩,
    oPrimeResidualOf_le_sSup h.toSec14Std.isE27 hbot hZY.2 hZΔ hD, hD⟩

theorem exists_mem_scriptY0_normalizer_of_at (hRead : Y4CoreReadR) {A L : Subgroup G} {c : G}
    (hMem : Y4CoreMemAt A) (h : Sec15R G A c L) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    {Y : Subgroup G} (hY : Y ∈ scriptY3 A (lB A)) (hO : oPrimeResidualOf 3 Y ≠ ⊥) {w : G}
    (hwA : w ∈ Subgroup.normalizer (A : Set G)) (hwY : w ∈ Subgroup.normalizer (Y : Set G))
    {n : ℕ} (hn : Odd n) (hwn : w ^ n = 1) :
    ∃ J ∈ scriptY0 A (lB A), w ∈ Subgroup.normalizer (J : Set G) := by
  obtain ⟨hM2, hF, hYM⟩ := twoLocal_facts h.toSec14Std hY.1
  set M := Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) with hM
  have hwM : w ∈ Subgroup.normalizer (M : Set G) :=
    Subgroup.le_normalizer (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y hwY)
  have hwZ : w ∈ Subgroup.normalizer ((delta A (lB A) M : Subgroup G) : Set G) :=
    Proof159.mem_normalizer_delta hwA hwM
  obtain ⟨⟨J₁, J₂, hS⟩, hJ, hOle, -⟩ := exists_mem_scriptY0_of_at hRead hMem h hbot hM2 hF
  have hne : oPrimeResidualOf 3 (delta A (lB A) M) ≠ ⊥ := fun h0 =>
    hO (le_bot_iff.mp (h0 ▸ oPrimeResidualOf_mono 3 (hY.2.le.trans (delta_mono hYM))))
  obtain ⟨J, hJ'⟩ := nonempty_of_le_sSup hOle hne
  exact ⟨J, (hJ J hJ').2, mem_normalizer_of_odd hS hwZ hn hwn hJ'⟩

theorem item1610_of_coreAt (hRead : Y4CoreReadR) {A L : Subgroup G} {c : G}
    (hMem : Y4CoreMemAt A) (h : Sec15R G A c L) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) :
    Sec16.Item1610 A (lB A) := by
  intro h0
  ext Y
  refine ⟨fun hY => ⟨hY, ?_⟩, fun hY => hY.1⟩
  by_contra hO
  obtain ⟨J, hJ, -⟩ := exists_mem_scriptY0_normalizer_of_at hRead hMem h hbot hY hO
    (Subgroup.one_mem _) (Subgroup.one_mem _) (by decide : Odd 1) (one_pow 1)
  rw [h0] at hJ
  exact hJ

section Certs

theorem y4CoreMemAt_of_not_allPointsHJ (h149 : Sec16.Item149S14) (hS : Y4CoreMemSolvR)
    (h134 : Item134) (h48 : Sec4.Item4_8) {A L : Subgroup G} {c : G} (h : Sec15R G A c L)
    (hHJ : ¬ AllPointsHJ A) : Y4CoreMemAt A := by
  intro M hM hF J hJ hAJ
  have h149' := h149 G A c L h.toSec14Std
  have hJM : J ∈ thetaComponentsIn M := mem_thetaComponentsIn_of_item149 h149' hM.1 hJ
  have hJtop : J ≠ ⊤ := fun h' =>
    hM.1.1 (top_le_iff.mp (h' ▸ le_of_mem_thetaComponentsIn hJM))
  have hJY : J ∈ scriptY A := ⟨hJtop, hAJ⟩
  have : Nontrivial ↥J := (Subgroup.nontrivial_iff_ne_bot J).mpr (ne_bot hJ)
  have hO2 : CFSG.pCore 2 ↥J ≠ ⊥ :=
    pCore_ne_bot_of_isCharacteristicP (isCharacteristicP_of_mem_thetaComponentsIn hF hJM)
  have hΔ : J = delta A (lB A) J :=
    eq_delta_of_not_isSolvable h149' hJM hJY (hS G A c L h M hM hF J hJ hAJ)
  have hq : IsQuasisimple (↥J ⧸ CFSG.pCore 2 ↥J) := by
    have hS4 : SectionFourHyp ↥J := h.toTheoremFourHyp.sectionFourHyp hJtop
    have hJp : Group.IsPerfect ↥J := isPerfect_of_mem_thetaComponentsIn hJM
    have hJq := isQuasisimple_theta_of_mem_thetaComponentsIn hJM
    have hθ := solvable_prime_complement_core_characterization (H := ↥J) Nat.prime_three
    set θ := aschbacherSolvableCore 3 ↥J
    set K := (Subgroup.center (↥J ⧸ θ)).comap (QuotientGroup.mk' θ)
    have hKn : K.Normal := Subgroup.Normal.comap inferInstance _
    have hKs : Group.IsSolvable K := isSolvable_comap_center θ hθ.1
    have : IsSimpleGroup ((↥J ⧸ θ) ⧸ Subgroup.center (↥J ⧸ θ)) := hJq.2.1
    have hKsimp : IsSimpleGroup (↥J ⧸ K) :=
      (quotientComapEquiv θ (Subgroup.center (↥J ⧸ θ))).isSimpleGroup
    rcases Sec4.item4_4OTwo_holds ↥J hS4 hJp K hKs hKsimp hO2 with h1 | h2 | ⟨p, hp, hp3, he⟩ | h4
    · exact h1
    ·
      exfalso
      obtain ⟨e⟩ := h2
      have : (Sec4.oTwoFitting ↥J).Characteristic := Proof15Res6.oTwoFitting_characteristic
      have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      exact Proof15Res6.false_of_sl2_nhj h134 h48 h hHJ hΔ hAJ (p := 5) le_rfl
        (Sec4.oTwoFitting ↥J) e
    ·
      exfalso
      have : Fact p.Prime := ⟨hp⟩
      have : (Sec4.oTwoP p ↥J).Characteristic := oTwoP_characteristic p
      have hp5 : 5 ≤ p := by
        rcases Nat.lt_or_ge p 5 with h5 | h5
        · interval_cases p
          exact absurd hp (by norm_num)
        · exact h5
      obtain ⟨e⟩ := he
      exact Proof15Res6.false_of_sl2_nhj h134 h48 h hHJ hΔ hAJ hp5 (Sec4.oTwoP p ↥J) e
    ·
      exact isQuasisimple_of_case444 hJp hJq h4
  exact ⟨⟨hJY, hJ.2, hΔ, hq⟩, ⟨hJY, pCoreOf_ne_bot_of_pCore_ne_bot hO2⟩⟩

theorem step159ClaimK_of_nhj (hRead : Y4CoreReadR) (h149 : Sec16.Item149S14)
    (hS : Y4CoreMemSolvR) (h134 : Item134) (h48 : Sec4.Item4_8) (hbot : Item145BotS14)
    (hK : Step159ClaimKY0) : Step159ClaimK := by
  intro G _ _ A c L ctx w hw V hV hwV hO
  have h := ctx.toSec15R
  obtain ⟨k, hwk⟩ := hw.2.1
  obtain ⟨J, hJ, hwJ⟩ := exists_mem_scriptY0_normalizer_of_at hRead
    (y4CoreMemAt_of_not_allPointsHJ h149 hS h134 h48 h (not_allPointsHJ_of_ctx159 ctx)) h
    (hbot G A c L h.toSec14Std) hV hO hw.1 hwV (Odd.pow (by decide : Odd 3)) hwk
  exact hK G A c L ctx w hw J hJ hwJ

theorem step159Y0Odd_of_nhj (hRead : Y4CoreReadR) (h149 : Sec16.Item149S14)
    (hS : Y4CoreMemSolvR) (h134 : Item134) (h48 : Sec4.Item4_8) (h146 : Item146S14)
    (h1411 : Item1411_3R) (hNT : Step159Y0NotTrans) : Step159Y0Odd := by
  intro G _ _ A c L ctx hO
  have h := ctx.toSec15R
  have hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥ :=
    ⟨A ⊓ L, ⟨inf_le_left, by rw [h.toSec13Data.card_eq, ctx.card_inf]⟩,
      Proof15Res3W.lB_eq_bot_of_ctx159 ctx _⟩
  have h1610 := item1610_of_coreAt hRead
    (y4CoreMemAt_of_not_allPointsHJ h149 hS h134 h48 h (not_allPointsHJ_of_ctx159 ctx)) h
    hbot
  have hStr := rank3II_14_11_3_strong_of h.toSec14Std.isE27 (h146 G A c L h.toSec14Std) hbot
    (h1411 G A c L h)
  exact Sec16.rank3II_16_9_1_of_not_transOn h.isElemAbelian.1 h.mem_A h1610 hStr
    (hNT G A c L ctx hO)

end Certs

end CFSG.RankThree.PartTwo.Sec15.Ronan154Big
