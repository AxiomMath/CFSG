module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148SRowM24
public import Certificates.Certificate148003
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.HeKFact

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148R

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.Sec4.RonanK429
open CFSG.RankThree.PartTwo.Sec4.Ronan148S
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.HeldB
open CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He CFSG.AGLEmbeddingD2.Wilson.Census219

section N0


@[expose] noncomputable def heN0 : Equiv.Perm (Fin 8330) := heThreeP heN0W

theorem heN0_mem : heN0 ∈ heP := heThreeP_mem _

theorem heN0_facts :
    (heN0 * bOf heThreeWordsA * heN0⁻¹) * bOf heThreeWordsA =
        bOf heThreeWordsA * (heN0 * bOf heThreeWordsA * heN0⁻¹) ∧
      heN0 * bOf heThreeWordsA * heN0⁻¹ ≠ 1 ∧
      heN0 * bOf heThreeWordsA * heN0⁻¹ ≠ bOf heThreeWordsA ∧
      heN0 * bOf heThreeWordsA * heN0⁻¹ ≠ bOf heThreeWordsA * bOf heThreeWordsA ∧
      heN0 * (heN0 * bOf heThreeWordsA * heN0⁻¹) * heN0⁻¹ =
        bOf heThreeWordsA * (heN0 * bOf heThreeWordsA * heN0⁻¹) := by
  have h := Certificates.certificate148003
  simp only [heN0Check, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hw, hwx⟩, hinv⟩, hcomm⟩, hne1⟩, hnex⟩, hnex2⟩, hmove⟩ := h
  have rN : Rep 8330 (heThreeArr heN0W) heN0 := rep_heThreeP hw
  have rNi : Rep 8330 (invCand 8330 (heThreeArr heN0W)) heN0⁻¹ := rep_inv_of_isInvA rN hinv
  have rX : Rep 8330 heThreeBA (bOf heThreeWordsA) := rep_heThreeP hwx
  have rF := rep_compA rN (rep_compA rX rNi)
  rw [← mul_assoc] at rF
  refine ⟨eq_of_eqA (rep_compA rF rX) (rep_compA rX rF) hcomm, fun h1 => ?_, fun h1 => ?_,
    fun h1 => ?_, ?_⟩
  · have := (eqA_iff rF rep_idA).2 h1
    rw [hne1] at this
    exact Bool.false_ne_true this
  · have := (eqA_iff rF rX).2 h1
    rw [hnex] at this
    exact Bool.false_ne_true this
  · have := (eqA_iff rF (rep_compA rX rX)).2 h1
    rw [hnex2] at this
    exact Bool.false_ne_true this
  · have h2 := eq_of_eqA (rep_compA rN (rep_compA rF rNi)) (rep_compA rX rF) hmove
    rw [← mul_assoc] at h2
    exact h2

end N0

section Surv


theorem survEAt_heY : SurvEAt heY (alternatingGroup (Fin 7)) := by
  intro K hK
  obtain ⟨-, ⟨e''⟩, hQ⟩ := he_layer
  have hCq : IsQuasisimple ↥(Subgroup.centralizer ({heY} : Set heP)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e''.symm heTc_spec.2.1
  have hnt : Nontrivial K := CFSG.LocalCores.isQuasisimple_nontrivial hK.isQuasisimple
  have hKeq : K = Subgroup.centralizer ({heY} : Set heP) :=
    Res429.eq_of_le_of_isSubnormal_of_isQuasisimple hK.le_centralizer hCq hK.isQuasisimple.1 hnt
      hK.isSubnormal
  refine ⟨isExtOf_congr ((MulEquiv.subgroupCongr hKeq).trans e'').symm hQ.isExtOf, ?_⟩
  obtain ⟨hc, hf1, hf2, hf3, hnf⟩ := heN0_facts
  obtain ⟨nP, hnv⟩ : ∃ nP : heP, (nP : Equiv.Perm (Fin 8330)) = heN0 := ⟨⟨heN0, heN0_mem⟩, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : heP, f = nP * heY * nP⁻¹ := ⟨_, rfl⟩
  have hyv : (heY : Equiv.Perm (Fin 8330)) = bOf heThreeWordsA := rfl
  have hfv : (f : Equiv.Perm (Fin 8330)) = heN0 * bOf heThreeWordsA * heN0⁻¹ := by
    rw [hf, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hnv, hyv]
  have hy3 : heY ^ 3 = 1 := by
    rw [← hK.orderOf_eq]
    exact pow_orderOf_eq_one _
  have hy1 : heY ≠ 1 := by
    intro h
    have := hK.orderOf_eq
    rw [h, orderOf_one] at this
    exact absurd this (by norm_num)
  have hyinv : heY⁻¹ = heY * heY := by
    rw [inv_eq_iff_mul_eq_one, ← pow_three]
    exact hy3
  have hc' : heY * f = f * heY := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hfv, hyv]
    exact hc.symm
  have hf1' : f ≠ 1 := fun h => hf1 (by rw [← hfv, h]; rfl)
  have hf2' : f ≠ heY := fun h => hf2 (by rw [← hfv, h, hyv])
  have hf3' : f ≠ heY⁻¹ := by
    intro h
    apply hf3
    rw [← hfv, h, hyinv, Subgroup.coe_mul, hyv]
  have hnf' : nP * f * nP⁻¹ = heY * f := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul, hfv, hyv, hnv]
    exact hnf
  have hfy3 : f ^ 3 = 1 := by rw [hf, conj_pow, hy3]; group
  have hfs := not_mem_zpowers_of_ne hy3 hf1' hf2' hf3'
  obtain ⟨hE, hE9⟩ := e9_of_commute hy3 hy1 hfy3 hc' hfs
  obtain ⟨hn, hns⟩ := move_of_conj hfs hf.symm hnf'
  refine ⟨Subgroup.zpowers heY ⊔ Subgroup.zpowers f, ?_, hE, hE9, nP, hn, hns⟩
  rw [hKeq]
  exact sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
    (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hc'.symm))

theorem survE_heP : SurvE heP (alternatingGroup (Fin 7)) := by
  refine survE_of_at fun s K hK => ?_
  have hord : orderOf (s : Equiv.Perm (Fin 8330)) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hK.orderOf_eq
  rcases three_conj_cases s.2 hord with ⟨c, hc, hcx⟩ | ⟨c, hc, hcx⟩
  · set gP : heP := ⟨c, hc⟩ with hgP
    set φ : heP ≃* heP := MulAut.conj gP⁻¹ with hφ
    have hφs : φ s = heY := by
      apply Subtype.ext
      have h1 : ((φ s : heP) : Equiv.Perm (Fin 8330)) = c⁻¹ * (s : Equiv.Perm (Fin 8330)) * c := by
        simp [hφ, hgP, MulAut.conj_apply]
      rw [h1, hcx]
      show c⁻¹ * (c * bOf heThreeWordsA * c⁻¹) * c = bOf heThreeWordsA
      group
    refine SurvEAt.of_mulEquiv φ ?_ K hK
    rw [hφs]
    exact survEAt_heY
  · exfalso
    set gP : heP := ⟨c, hc⟩ with hgP
    set φ : heP ≃* heP := MulAut.conj gP⁻¹ with hφ
    have hφs : ((φ s : heP) : Equiv.Perm (Fin 8330)) = bOf heThreeWordsB := by
      have h1 : ((φ s : heP) : Equiv.Perm (Fin 8330)) = c⁻¹ * (s : Equiv.Perm (Fin 8330)) * c := by
        simp [hφ, hgP, MulAut.conj_apply]
      rw [h1, hcx]
      group
    have hcard : Nat.card ↥(Subgroup.centralizer ({φ s} : Set heP)) = 504 := by
      rw [card_centralizer_heP, hφs]
      exact card_cent_B
    exact goodCC425_of_card_dvd (M := 504) (B := 8) hcard.dvd (by norm_num) (by norm_num)
      (by decide +kernel) _ (hK.map φ)

end Surv

section Row

theorem checkSL_he : ∀ q < 1592, 2 ≤ q → q ^ 3 ∣ 4030387200 →
    4030387200 * Nat.gcd 3 (q - 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  decide +kernel

theorem checkSU_he : ∀ q < 1592, 2 ≤ q → q ^ 3 ∣ 4030387200 →
    4030387200 * Nat.gcd 3 (q + 1) ≠ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) := by
  decide +kernel


theorem rankTwo_spor_he : RankTwoData (Spor .He) := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.Carrier .He ≃* Spor .He := b
  have hcard : Nat.card (Spor .He) = 4030387200 := by
    rw [← Nat.card_congr b'.toEquiv]
    exact CFSG.Sporadic.He.card_He
  haveI : Finite (Spor .He) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hrank : CFSG.pRank 3 (Spor .He) = 2 :=
    (CFSG.RankThree.Asc83Table.He.table (L := Spor .He) ⟨b'.symm⟩).2.1
  refine ⟨cubeInner_of_not_three_dvd_card_outer spor_he.1, fun E hE => ?_, ?_⟩
  · have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup (Spor .He)) ≤ 2 := by
      rw [← CFSG.SectionRank.pRank_eq_open_pRank_top 3 (Spor .He)]
      exact hrank.le
    exact (card_le_of_pRank_le h2 hE).trans (by norm_num)
  · exact exists_e9_of_pRank_eq_two
      ((CFSG.SectionRank.pRank_eq_open_pRank_top 3 (Spor .He)).symm.trans hrank)

end Row

section RowHe


theorem rowOf425_he
    : RowOf425 (Spor .He) := by
  intro S _ _ _ _ ⟨e⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.He.nonempty_mulEquiv
  have b' : Blueprint.NativeSporadic.He ≃* Spor .He := b
  refine row425_of_survE ?_ (RankTwoData.of_mulEquiv e rankTwo_spor_he)
    (Or.inr ⟨⟨e.trans b'.symm⟩,
      SurvE.of_mulEquiv ((e.trans b'.symm).trans heEquivP) survE_heP⟩)
  intro L _ _ hS hL hZ3 ⟨e'⟩
  have hc : Nat.card (L ⧸ Subgroup.center L) = 4030387200 := by
    rw [Nat.card_congr ((e'.trans e).trans b'.symm).toEquiv, CFSG.Sporadic.He.card_He]
  exact center_eq_bot_of_card hS hL hZ3 (N := 4030387200) hc
    (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) checkSL_he)
    (KFacts.KS14.forall_of_forall_lt (by norm_num) (by norm_num) checkSU_he)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end RowHe

end CFSG.RankThree.PartTwo.Sec4.Ronan148R

end
