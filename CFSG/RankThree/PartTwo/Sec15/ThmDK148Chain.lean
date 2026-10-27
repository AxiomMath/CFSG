module

public import CFSG.RankThree.PartTwo.Sec15.ThmDFront
public import CFSG.RankThree.PartTwo.Sec15.ThmDK148Defs
import CFSG.RankThree.PartTwo.Sec14.Item148Proof
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKType
import CFSG.RankThree.PartTwo.Sec14.Item148Res4ProofTen
import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofCases
import CFSG.RankThree.PartTwo.Sec15.F153L3C2Order
public import CFSG.RankThree.PartTwo.Sec14.Item148StepCases

public section

namespace CFSG.RankThree.PartTwo.Sec15.ThmD

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement Pointwise

section Chain


theorem step148FourKFact'_of_steps (hYB : Step148YB) (hHJ : Step148HJ) (hCore : Step148Core)
    (hPoint : Step148Point) (hKT : Step148KType) (hLift : Step148Lift) (hD4 : Step148D4)
    (h148 : Item148R) (h134 : Item134) (h48 : Sec4.Item4_8) : Step148FourKFact' := by
  intro G _ _ A c L hR Y hY0 hYΔ hcen h10 _hL7 _hW
  unfold Print148FourK
  have hS : Sec14Std G A c L := hR.toSec14Std
  have hAab : IsMulCommutative A := hR.isElemAbelian.1
  have hY4 : Y ∈ scriptY4 A (lB A) := hY0.1
  have hY : Y ∈ scriptY A := hY4.1
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hY.2
  let := ker148_normal hAY
  have hq := Proof1515.isQuasisimple_quot_pPrimeCore hY4
  have hne := Proof1515.pPrimeCore_ne_top_of_mem_scriptY4 hY4
  obtain ⟨eYY⟩ : Nonempty (↥(img148 A Y Y) ≃* ↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) :=
    nonempty_img148_equiv hAY
  obtain ⟨e0⟩ : Nonempty (↥(img148 A Y (deltaZero A (lB A) Y)) ≃* ↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) := by
    rw [← hYΔ]
    exact ⟨eYY⟩
  have hqX : IsQuasisimple ↥(img148 A Y (deltaZero A (lB A) Y)) :=
    CFSG.LocalCores.isQuasisimple_of_surjective hq e0.symm.toMonoidHom e0.symm.surjective
      (by rw [(MonoidHom.ker_eq_bot_iff _).mpr e0.symm.injective]; exact bot_le)
  have := Proof1515.nontrivial_alternatingGroup_five
  have := Proof1515.nontrivial_J2
  have hAA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hfalse1 : Case148One A (lB A) Y → False := by
    intro h1
    apply hne
    have h1' : deltaZero A (lB A) Y ≤ pPrimeCoreOf 3 Y := h1
    rw [← hYΔ] at h1'
    refine eq_top_iff.mpr fun y _ => ?_
    obtain ⟨z, hz, hzy⟩ := h1' y.2
    rwa [show z = y from Subtype.ext hzy] at hz
  have hfalse2 : (∃ a ∈ A, a ≠ 1 ∧ ⁅Y, Subgroup.zpowers a⁆ ≤ pPrimeCoreOf 3 Y) → False := by
    rintro ⟨a, haA, ha1, hYa⟩
    exact hcen ⟨a, haA, ha1, (ThmC.lemma7_centralizes hY0 haA hYa).1⟩
  have hfalseTwo : Case148Two A (lB A) Y → False := by
    rintro ⟨c', hc', hdec, -⟩
    rw [← hYΔ] at hdec
    obtain ⟨hcA, hc3, -⟩ := zpowers_mem_omegaA_iff.mp hc'
    have hc1 : c' ≠ 1 := fun h => by
      rw [h, Subgroup.zpowers_one_eq_bot] at hc3
      simp at hc3
    refine hfalse2 ⟨c', hcA, hc1, commutator_zpowers_le_pPrimeCoreOf_of_dec hcA hAY ?_ hdec⟩
    exact Proof1511Point.deltaZero_le_centralizer hAA (lB A) hcA inf_le_right
  have hfalseThree : Case148Three A (lB A) Y → False := by
    rintro ⟨c', d, L', hc', hL', hJ, hdA, hd1, hdc, hdec, -⟩
    rw [← hYΔ] at hdec
    refine hfalse2 ⟨d, hdA, hd1, commutator_zpowers_le_pPrimeCoreOf_of_dec hdA hAY ?_ hdec⟩
    exact (deltaZero_le _).trans inf_le_right
  have hfalseSix : Case148Six A (lB A) Y → False := by
    rintro ⟨hφ, -⟩
    obtain ⟨φ⟩ := hφ
    exact ((Proof1515.isEmpty_mulEquiv_prod_of_isQuasisimple hqX).false φ).elim
  have hs : ¬ Group.IsSolvable ↥Y := fun hs =>
    hfalse1 (item148Solvable_of_mem_partTwoF hS.mem_partTwoF Y hY hs)
  have ih : Ind148 A (lB A) Y := fun Y' hY' _ => h148 G A c L hR Y' hY'
  by_cases hHJb : ∃ B, IsHyperplane A B ∧ ¬ YBOne A (lB A) Y B
  · obtain ⟨B, hB, hnot⟩ := hHJb
    obtain ⟨YB, hYB', htype, hle, b, d, Lb, hconf, hYBle⟩ := hYB G A c L hS Y hY hs B hB hnot
    rcases hHJ G A c L hS Y hY hs ih B hB hnot YB hYB' htype hle b d Lb hconf hYBle with
      h2 | h3 | h6
    · exact (hfalseTwo h2).elim
    · exact (hfalseThree h3).elim
    · exact (hfalseSix h6).elim
  push Not at hHJb
  have hYB1 : ∀ B : Subgroup G, IsHyperplane A B → YBOne A (lB A) Y B := hHJb
  by_cases hcore : ∀ B : Subgroup G, IsHyperplane A B → ∀ Q ∈ scriptQZero A (lB A),
      Q ≤ Y ⊓ Subgroup.centralizer (B : Set G) →
      ∀ b ∈ B, b ≠ 1 → Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G))
  · exact (hfalse1 (case148One_of_core hCore hS hY hs hYB1 hcore)).elim
  push Not at hcore
  obtain ⟨B, hB, Q, hQ, hQY, b, hb, hb1, hQb⟩ := hcore
  obtain ⟨e, K, Le, hP⟩ := hPoint G A c L hS Y hY hs hYB1 B hB Q hQ hQY b hb hb1 hQb
  have hkt : KType148 A Y e K Le := hKT G A c L hS Y hY hs hYB1 B Q e K Le hP
  have heA : e ∈ A := hB.1 hP.2.2.2.1
  have he1 : e ≠ 1 := hP.2.2.2.2.1
  have hK : K ∈ thetaComponentsIn (Y ⊓ Subgroup.centralizer ({e} : Set G)) :=
    hP.2.2.2.2.2.1
  have hKΔ : K = deltaZero A (lB A) K := hP.2.2.2.2.2.2.1
  obtain ⟨J, hJ, hKJ, hAJ, halt⟩ := hLift G A c L hS Y hY hs e heA he1 K hK
    (le_normalizer_of_eq_deltaZero hKΔ) hkt.1 (type148_of_kType148 hS.chosen136 hkt)
  have hKY : K ≤ Y ⊓ Subgroup.centralizer ({e} : Set G) := le_of_mem_thetaComponentsIn hK
  have hKY' : K ≤ Y := hKY.trans inf_le_left
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have h3K : 3 ∣ Nat.card ↥(img148 A Y K) := Main148.three_dvd_card_img148_of_types hS hkt.2
  obtain ⟨-, hJ'⟩ := mem_thetaComponentsIn_iff.mp hJ
  obtain ⟨eK⟩ := Y4Core.nonempty_img148_equiv_map hAY hKY'
  obtain ⟨eJ⟩ := Y4Core.nonempty_img148_equiv_map hAY hJY
  obtain ⟨φ10⟩ := h10
  have : IsSimpleGroup (alternatingGroup (Fin 10)) := alternatingGroup.isSimpleGroup (by simp)
  have hs' : IsSimpleGroup (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) := φ10.isSimpleGroup
  have hJtop : (J.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y)) = ⊤ := by
    rcases (hJ'.2.1.map (QuotientGroup.mk'_surjective _)).eq_bot_or_top_of_isSimpleGroup hs' with
      hbot | htop
    · exfalso
      have hK1 : (K.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y)) = ⊥ :=
        le_bot_iff.mp ((Subgroup.map_mono (Subgroup.subgroupOf_mono Y hKJ)).trans hbot.le)
      have hc := Nat.card_congr eK.toEquiv
      rw [hK1, Subgroup.card_bot] at hc
      rw [hc] at h3K
      omega
    · exact htop
  have eJY : ↥(img148 A Y J) ≃* ↥Y ⧸ CFSG.pPrimeCore 3 ↥Y :=
    (eJ.trans (MulEquiv.subgroupCongr hJtop)).trans Subgroup.topEquiv
  have hJYeq : img148 A Y J = img148 A Y Y := by
    refine Subgroup.eq_of_le_of_card_ge (img148_mono hJY) ?_
    exact ((Nat.card_congr eYY.toEquiv).trans (Nat.card_congr eJY.toEquiv).symm).le
  rcases halt with hEq | hTen | ⟨m, hm, -, hJπ, -⟩ | hD
  ·
    have hEq' : img148 A Y K = img148 A Y J := hEq
    have hXK : img148 A Y (deltaZero A (lB A) Y) = img148 A Y K := by
      rw [← hYΔ, hEq', hJYeq]
    rcases case148Two_or_of_img148_eq hXK hKY hKΔ hkt with h2 | ⟨hON, htype⟩
    · exact (hfalseTwo h2).elim
    · exact (hfalseThree (case148Three_of_img148_eq hS hXK hP hON htype)).elim
  ·
    rcases hP.2.2.2.2.2.2.2.2.2 with ⟨heΩ, -⟩ | ⟨c', L', hc'Ω, -, hL'A, hJ2, hcent, -⟩
    ·
      obtain ⟨φ⟩ := hTen.1
      exact ⟨e, heA, heΩ, K, hKY, ⟨eK.symm.trans φ⟩⟩
    ·
      exfalso
      have hAF : A ∈ partTwoF G := hS.mem_partTwoF
      have hle : img148 A Y A ≤ img148 A Y J :=
        Item148Rank.img148_le_of_lift148Ten148 hAF hAY heA hK hKJ hJY hAJ hkt.1 hTen
      have hirr : Sec21.IsIrreducibleOn (wStar A) :=
        Item148Rank.isIrreducibleOn_wStar148 hS.isE27 hle hTen.2
      exact Item148Res4.not_isIrreducibleOn_of_hj_point h134 h48 hS hc'Ω hL'A hJ2 heA he1 hcent
        hirr
  ·
    exfalso
    have ψ : ↥(img148 A Y J) ≃* alternatingGroup (Fin 10) := eJY.trans φ10
    haveI : Group.IsPerfect (↥Y ⧸ CFSG.pPrimeCore 3 ↥Y) := hq.1
    haveI : Nontrivial ↥(img148 A Y J) := ψ.symm.injective.nontrivial
    haveI : Group.IsPerfect ↥(img148 A Y J) :=
      Group.IsPerfect.ofSurjective (f := eJY.symm.toMonoidHom) eJY.symm.surjective
    have hε := isLThreeEpsAt_of_isoLThreePi148 hJπ
    exact ((F153L3C2.kL3Char2NotList148_holds ↥(img148 A Y J) (3 * m) (by omega) hε).2.2.2.1).false
      ψ
  ·
    exact (hD4 G A c L hS Y hY hs hYB1 B Q e K Le hP hkt heA J hJ hKJ hAJ hD).elim

end Chain

end CFSG.RankThree.PartTwo.Sec15.ThmD
