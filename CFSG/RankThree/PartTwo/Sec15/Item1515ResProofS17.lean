module

import CFSG.RankThree.PartTwo.Sec14.Concl142HJPoint
import CFSG.RankThree.PartTwo.Sec15.Item1514StepsHJ
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.Sporadic.ON
public import CFSG.RankThree.PartTwo.Sec13.Item136PGL
public import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1515S17
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsQuot
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsRoute
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsS17
public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofA7
public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofM22
public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofON
public import CFSG.RankThree.PartTwo.Sec15.Item156ProofType
public import CFSG.RankThree.PartTwo.Sec17.Item175Proof

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec17 CFSG.RankThree.LocalRank
  CFSG.GH74.GLS

@[expose] noncomputable def Step1515HJListLe : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ Y ∈ scriptY0Star A (lB A), L ≤ Y →
      Nonempty (↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin 5)) ∨
      Sec4.IsTripleCover (↥Y ⧸ CFSG.pCore 2 ↥Y) (alternatingGroup (Fin 6)) ∨
      Sec4.IsTripleCover (↥Y ⧸ CFSG.pCore 2 ↥Y) CFSG.Blueprint.NativeSporadic.ON ∨
      (Y = (Y ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y ∧ L = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 L)

namespace Proof1515Res

variable {G : Type} [Group G] [Finite G]

theorem eq_sup_pCoreOf_two_of_le_of_card {L Y : Subgroup G} (hLY : L ≤ Y)
    (hcard : Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) ≤ Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
    Y = L ⊔ CFSG.Open.pCoreOf 2 Y := by
  set f := (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).comp (Subgroup.inclusion hLY) with hf
  have hker : f.ker ≤ aschbacherSolvableCore 3 ↥L := Proof1514.ker_toQuotTwo_le hLY
  have h1 : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) ≤ Nat.card (↥L ⧸ f.ker) :=
    Proof1515.card_quotient_le_of_le hker
  have h2 : Nat.card (↥L ⧸ f.ker) = Nat.card f.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  have h3 : Nat.card f.range = Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
    le_antisymm (Subgroup.card_le_card_group _) (by omega)
  have hsurj : Function.Surjective f :=
    MonoidHom.range_eq_top.mp (Subgroup.eq_top_of_card_eq _ h3)
  refine le_antisymm (fun y hy => ?_) (sup_le hLY (CFSG.LieType.BorelTits.pCoreOf_le 2 Y))
  obtain ⟨x, hx⟩ := hsurj (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨y, hy⟩)
  rw [hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq] at hx
  have hmem : ((Subgroup.inclusion hLY x)⁻¹ * ⟨y, hy⟩ : ↥Y) ∈ CFSG.Open.pCore 2 ↥Y := by
    exact hx
  have hy' : y = (x : G) * (((Subgroup.inclusion hLY x)⁻¹ * ⟨y, hy⟩ : ↥Y) : G) := by simp
  rw [hy']
  exact mul_mem (Subgroup.mem_sup_left x.2) (Subgroup.mem_sup_right ⟨_, hmem, rfl⟩)

end Proof1515Res

open Proof1515 Proof1514 Proof1515Res

section List


theorem step1515HJListLe_of
    (h148 : Item148R) (hbot : Item145BotS14) (h134 : Item134)
    (h48 : Sec4.Item4_8) : Step1515HJListLe := by
  intro G _ _ A c L h hJ Y hY hLY
  obtain ⟨φL⟩ := hJ
  have hY4 : Y ∈ scriptY4 A (lB A) := hY.prop.1
  have hYΔ := eq_deltaZero_of_mem_scriptY4 hbot h hY4
  have hne := pPrimeCore_ne_top_of_mem_scriptY4 hY4
  have hJc : Nat.card CFSG.Blueprint.NativeSporadic.J2 = 604800 := KFacts.KS14.card_nativeJ2
  have hLJ : Nat.card (↥L ⧸ aschbacherSolvableCore 3 ↥L) = 604800 := by
    rw [Nat.card_congr φL.toEquiv, hJc]
  have hdvd : 604800 ∣ Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) := hLJ ▸ card_thetaQuot_dvd hLY
  have hall := allPointsHJ_of_j2 h134 h48 h.toSec14Std ⟨φL⟩
  have h3J : 3 ∣ Nat.card CFSG.Blueprint.NativeSporadic.J2 := by rw [hJc]; norm_num
  have hpt : ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2) := by
    intro c' L' hc' hL'
    obtain ⟨Le, hLe, hJe⟩ := hall c' hc'
    obtain ⟨φe⟩ := hJe
    have h3e : 3 ∣ Nat.card Le :=
      three_dvd_card_of_thetaQuot ((Nat.card_congr φe.toEquiv).symm ▸ h3J)
    have heq := (h.chosen136.2 c' hc' L' hL').2 Le hLe.1 h3e
    rw [← heq]
    exact ⟨φe⟩
  have hptc : ∀ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A → L' ∈ lA A c' →
      Nat.card (↥L' ⧸ aschbacherSolvableCore 3 ↥L') = 604800 := by
    intro c' L' hc' hL'
    obtain ⟨φ'⟩ := hpt c' L' hc' hL'
    rw [Nat.card_congr φ'.toEquiv, hJc]
  rcases cases148_of_mem_scriptY4 (h148 G A c L h) h.isElemAbelian.1 hY4 hYΔ with
    ⟨c', hc', -, L', hL', hcases⟩ | ⟨c', L', hc', hL', -, h3⟩ |
      ⟨-, ⟨c', L', hc', hL', ⟨φ7⟩⟩, -⟩ | ⟨c', L', n, m, hc', hL', -, -, -, hε⟩
  · obtain ⟨φJ'⟩ := hpt c' L' hc' hL'
    rcases hcases with hφ | ⟨hL'', -⟩ | ⟨p, f, e, hp, -, -, hiso, -⟩ | ⟨-, h6 | h5⟩
    ·
      obtain ⟨φ⟩ := hφ
      obtain ⟨φY⟩ := nonempty_quot_pCore_two_equiv_of_multFree hY4 ⟨φ.trans φJ'⟩ multFree_J2
      refine Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))
      · rw [inf_eq_right.mpr hLY]
        exact eq_sup_pCoreOf_two_of_le_of_card hLY
          (by rw [Nat.card_congr φY.toEquiv, hJc, hLJ])
      · rw [inf_eq_left.mpr hLY]
        exact (sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 L)).symm
    ·
      exfalso
      rcases hL'' with hM | ⟨_, hφ⟩ | ⟨_, hφ⟩
      · obtain ⟨φM⟩ := hM
        have h1 := hptc c' L' hc' hL'
        rw [Nat.card_congr φM.toEquiv, KFacts.KS14.card_nativeM22] at h1
        omega
      · obtain ⟨φ⟩ := hφ
        exact Proof1514.not_isoLThreePi_of_j2 φJ' (p := 5) (e := 2) (Or.inl ⟨by norm_num, ⟨φ⟩⟩)
      · obtain ⟨φ⟩ := hφ
        exact Proof1514.not_isoLThreePi_of_j2 φJ' (p := 5) (e := 1) (Or.inr ⟨by norm_num, ⟨φ⟩⟩)
    ·
      exact (Proof1514.not_isoLThreePi_of_j2 φJ' hiso).elim
    ·
      have hc : Nat.card (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) = 1080 := by
        rw [card_of_isTripleCover h6, card_alternatingGroup_six]
      have heq := pPrimeCore_three_eq_pCore_two_of_not_sq_dvd hY4.2.2.2 hne
        fun p hp hp6 => hc ▸ not_sq_dvd_small (Or.inr rfl) hp hp6
      exact Or.inr (Or.inl (isTripleCover_congr (QuotientGroup.quotientMulEquivOfEq heq) h6))
    ·
      obtain ⟨φ⟩ := h5
      have hc : Nat.card (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) = 60 := by
        rw [Nat.card_congr φ.toEquiv, card_alternatingGroup_five]
      have heq := pPrimeCore_three_eq_pCore_two_of_not_sq_dvd hY4.2.2.2 hne
        fun p hp hp6 => hc ▸ not_sq_dvd_small (Or.inl rfl) hp hp6
      exact Or.inl ⟨(QuotientGroup.quotientMulEquivOfEq heq).symm.trans φ⟩
  ·
    rcases h3 with hON' | hφ | ⟨_, hφ⟩
    ·
      have heq := pPrimeCore_three_eq_pCore_two_of hY4.2.2.2 hne fun Z _ hZc hcop ⟨φ⟩ =>
        ks1515ONMult _ Z hY4.2.2.2.1 hZc hcop (isTripleCover_congr φ.symm hON')
      exact Or.inr (Or.inr (Or.inl (isTripleCover_congr (QuotientGroup.quotientMulEquivOfEq heq)
        hON')))
    ·
      exfalso
      obtain ⟨φY⟩ := nonempty_quot_pCore_two_equiv_of_multFree hY4 hφ
        multFree_alternatingGroup_seven
      rw [Nat.card_congr φY.toEquiv, card_alternatingGroup_seven] at hdvd
      norm_num at hdvd
    ·
      exfalso
      obtain ⟨φ⟩ := hφ
      have hL3 : IsLThreePi (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)) :=
        ⟨7, 1, inferInstance, le_rfl, Or.inl ⟨by norm_num, ⟨MulEquiv.refl _⟩⟩⟩
      obtain ⟨φY⟩ := nonempty_quot_pCore_two_equiv_of_multFree hY4 ⟨φ⟩
        (multFree_of_isLThreePi hL3)
      rw [Nat.card_congr φY.toEquiv, card_projSL_three_seven] at hdvd
      norm_num at hdvd
  ·
    exfalso
    have h1 := hptc c' L' hc' hL'
    rw [Nat.card_congr φ7.toEquiv, card_alternatingGroup_seven] at h1
    omega
  ·
    exact (not_isLThreeEpsAt_of_card_j2 (hptc c' L' hc' hL') 2 (n * m) hε).elim

end List

section S17

variable {G : Type} [Group G] [Finite G]

theorem rank3II_15_15_S17_of_le
    {A : Subgroup G} {c : G}
    {L Y₀ : Subgroup G} (h : Sec17Std G A c L Y₀) (h131 : Item131) (h137 : Item137)
    (h1511 : Item1511 A (lB A) c L) (h1513 : Item1513 A (lB A) c L)
    (hA7O : Step1515A7Omega) (hM22 : Step1515M22) (hHJL : Step1515HJListLe) :
    Step1515 A (lB A) c L := by
  intro Y hY hm hce
  have hR := h.toSec15R
  have hD := h.toSec13Data
  have hYY : Y = Y₀ := h.eq_of_mem_y0Star hY
  have hLY : L ≤ Y := hYY ▸ h.le_y0
  have hq : IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) := hY.prop.1.2.2.2
  have hO : L = (L ⊓ Y) ⊔ CFSG.Open.pCoreOf 2 L := by
    rw [inf_eq_left.mpr hLY]
    exact (sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 L)).symm
  obtain ⟨⟨hM22p, hM22z⟩, ⟨hM12p, hM12z⟩, ⟨hJ2p, hJ2z⟩⟩ := sporadicModels131
  have hAHY : A ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.normalizer (Y : Set G) :=
    le_inf (hD.A_le_centralizer.trans (centralizer_singleton_le_normalizer_zpowers c))
      hY.prop.1.1.2
  have hA3 : IsPGroup 3 A := IsPGroup.of_card (n := 3) (by rw [hD.card_eq]; norm_num)
  obtain ⟨P, hP, hAP⟩ := Item134SylowBarProof.exists_isSylowOf_le hAHY hA3
  rcases cases131 h131 sporadicModels131 slTwoCenter hD with
    ⟨hcL, h9, hprod, hcase⟩ | ⟨-, -, hMJ, -⟩ | ⟨hcL, hPGL, -, -⟩ | ⟨hcL, -⟩
  ·
    have hirr := isIrreducibleOn_of_cases131 hD hcL h9 hcase
    rcases h1513 ⟨Y, hY.prop⟩ hirr h9 with ⟨hL7, hWS, -, hT⟩ | hΩ
    ·
      have hne : omegaA A ≠ {Subgroup.zpowers c} := by
        intro hΩ
        have h3 := hT.1
        rw [hΩ, Set.ncard_singleton] at h3
        omega
      have h10 := h.a10_or_omega.resolve_right hne
      rw [← hYY] at h10
      exact (hce (Or.inr (Or.inl ⟨hL7, hWS, hT, Or.inr h10⟩))).elim
    · rcases hcase with ⟨⟨p, e, hp, he, hiso⟩, -⟩ | ⟨hL7, -⟩ | ⟨hL22, -⟩
      ·
        obtain ⟨hprod', -, hYL, hcases, -⟩ := h1511 p e he hiso Y hY.prop hm P hAP hP
        rcases hcases with hε | hY7
        · exact ⟨p, e, hp, he, hiso, hprod', hYL, hε, hΩ⟩
        ·
          exfalso
          have hYL' : Y = L ⊔ CFSG.Open.pCoreOf 2 Y := by
            rwa [inf_eq_left.mpr hLY] at hYL
          obtain ⟨φ⟩ := hY7
          have hcard := card_thetaQuot_eq hLY hYL'
            (isSimpleGroup_of_mulEquiv_alternating (by norm_num) φ) hq.1
          rw [Nat.card_congr φ.toEquiv,
            KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1] at hcard
          exact not_isoLThreePi_of_card_2520 hcard p e hiso
      ·
        obtain ⟨hYL, hLY'⟩ := hA7O G A c L hR hL7 hΩ Y hY hm
        exact (hce (Or.inl ⟨hYL, hLY', hΩ, hprod, isEmpty_mulEquiv_M12_of_A7 hL7.some⟩)).elim
      ·
        have hYL := hM22 G A c L hR hL22 hΩ Y hY hm
        exact (hce (Or.inl ⟨by rwa [inf_comm], hO, hΩ, hprod,
          isEmpty_mulEquiv_M12_of_M22 hL22.some⟩)).elim
  ·
    rcases hMJ with hψ | hψ
    · obtain ⟨ψ⟩ := hψ
      obtain ⟨-, -, -, hM12⟩ := facts_of_prod hD hM12p hM12z ψ
      exact (false_of_m12_of_le hR h137 hM12 hY.prop.2 hLY le_rfl hD.le_normalizer
        (by rw [Subgroup.relIndex_self]; norm_num)).elim
    · obtain ⟨ψ⟩ := hψ
      obtain ⟨-, -, hprod, ⟨φJ⟩⟩ := facts_of_prod hD hJ2p hJ2z ψ
      have hdvd := card_thetaQuot_dvd hLY
      rw [Nat.card_congr φJ.toEquiv, KFacts.KS14.card_nativeJ2] at hdvd
      rcases hHJL G A c L hR ⟨φJ⟩ Y hY hLY with h5 | h6 | hON | ⟨hYL, -⟩
      · obtain ⟨ψ5⟩ := h5
        rw [Nat.card_congr ψ5.toEquiv, KFacts.KS14.card_alternatingGroup_five_seven_ten.1]
          at hdvd
        exact absurd hdvd (by norm_num)
      · rw [card_eq_of_isTripleCover h6, KFacts.KS14.card_alternatingGroup_fin (by norm_num)]
          at hdvd
        exact absurd hdvd (by decide)
      · rw [card_eq_of_isTripleCover hON, CFSG.Sporadic.ON.card_ON] at hdvd
        exact absurd hdvd (by norm_num)
      · by_cases hΩ : omegaA A = {Subgroup.zpowers c}
        · exact (hce (Or.inl ⟨hYL, hO, hΩ, hprod, isEmpty_mulEquiv_M12_of_J2 φJ⟩)).elim
        ·
          exfalso
          have h10 := h.a10_or_omega.resolve_right hΩ
          rw [← hYY] at h10
          obtain ⟨φ⟩ := h10
          have hYL' : Y = L ⊔ CFSG.Open.pCoreOf 2 Y := by
            rwa [inf_eq_right.mpr hLY] at hYL
          have hcard := card_thetaQuot_eq hLY hYL'
            (isSimpleGroup_of_mulEquiv_alternating (by norm_num) φ) hq.1
          rw [Nat.card_congr φJ.toEquiv, KFacts.KS14.card_nativeJ2, Nat.card_congr φ.toEquiv,
            KFacts.KS14.card_alternatingGroup_five_seven_ten.2.2] at hcard
          omega
  ·
    obtain ⟨⟨p, e, hp, he, hiso⟩, -, -⟩ := facts_of_isZ3PGLThreePi hD hPGL
    obtain ⟨hprod', -⟩ := h1511 p e he hiso Y hY.prop hm P hAP hP
    exact (false_of_prod_of_isZ3PGLThreePi hD hcL hprod' hPGL).elim
  ·
    exact (hR.hypS.2.2 c hR.zpowers_mem_omegaA L hR.mem_lA hcL).elim

end S17

theorem step1515S17_of_res
    (h131 : Item131)
    (h137 : Item137) (h1511 : Item1511S17)
    (h1513 : Item1513S17) (hA7O : Step1515A7Omega) (hM22 : Step1515M22)
    (hHJL : Step1515HJListLe) : Step1515S17 :=
  fun G _ _ A c L Y₀ hs => rank3II_15_15_S17_of_le hs h131 h137 (h1511 G A c L Y₀ hs)
    (h1513 G A c L Y₀ hs) hA7O hM22 hHJL

theorem item1514S17_of_res
    (h131 : Item131) (h137 : Item137) (h1511 : Item1511S17)
    (h1513 : Item1513S17) (h148 : Item148R) (hbot : Item145BotS14) (h142 : Item142R)
    (h134 : Item134) (h48 : Sec4.Item4_8) (h135 : Item135) : Item1514S17 :=
  fun G _ _ A c L Y₀ hs => rank3II_15_14_of_steps
    (step1515S17_of_res h131 h137 h1511 h1513 (step1515A7Omega_of h148 hbot h131 h135)
      (step1515M22_of h148 hbot h142) (step1515HJListLe_of h148 hbot h134 h48)
      G A c L Y₀ hs)
    (step1519S17 G A c L Y₀ hs) (step1521S17 G A c L Y₀ hs) (step1522S17 G A c L Y₀ hs)

end CFSG.RankThree.PartTwo.Sec15
