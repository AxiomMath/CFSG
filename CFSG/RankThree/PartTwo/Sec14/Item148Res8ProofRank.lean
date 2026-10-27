module

public import CFSG.RankThree.PartTwo.Sec14.Item148Res6ProofRank
import CFSG.RankThree.PartTwo.Sec14.Item148RankProofChar
import CFSG.RankThree.PartTwo.Sec6.Item612Local
public import CFSG.RankThree.PartTwo.Sec14.Item148Res4ProofTen
public import CFSG.RankThree.PartTwo.Sec14.Item148Res5ProofRank
public import CFSG.RankThree.PartTwo.Sec14.Item148Res6ProofFieldTop

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open Item148Res4 Item148Res6

namespace Item148Res8

section Steps


theorem step148Rank_of_res8
    (hD : Step148RankImgGeFieldTopDich) (h133 : Item133)
    (h134 : Item134) (h48 : Sec4.Item4_8) (hFive : Step148RankFive) : Step148Rank := by
  intro G _ _ A c L h Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ halt hA
  let := ker148_normal hY.2
  have hKY : K ≤ Y ⊓ Subgroup.centralizer ({e} : Set G) :=
    le_of_mem_thetaComponentsIn hP.2.2.2.2.2.1
  have hKY' : K ≤ Y := hKY.trans inf_le_left
  have hKΔ : K = deltaZero A (lB A) K := hP.2.2.2.2.2.2.1
  have hKX : K ≤ deltaZero A (lB A) Y := hKΔ.le.trans (deltaZero_mono148 hKY')
  by_cases hbad : ∃ _ : Lift148Field A Y e he K J, J = Y ∧
      ¬ img148 A Y J ≤ img148 A Y (deltaZero A (lB A) Y)
  · obtain ⟨hF, hJY, hnot⟩ := hbad
    have hXK : img148 A Y (deltaZero A (lB A) Y) = img148 A Y K :=
      le_antisymm ((hD G A c L h Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hF hA
        hJY).resolve_left hnot) (img148_mono hKX)
    rcases case148Two_or_of_img148_eq hXK hKY hKΔ hkt with h2 | ⟨hON, htype⟩
    · exact Or.inl h2
    · exact Or.inr (Or.inl (case148Three_of_img148_eq h hXK hP hON htype))
  push Not at hbad
  have hGe : img148 A Y J ≤ img148 A Y (deltaZero A (lB A) Y) := by
    rcases halt with hEq | hTen | hField
    · exact img148_le_of_lift148Eq hKY' hKΔ hEq
    · exact step148RankImgGe_ten G A c L h Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hTen
        hA
    · by_cases hJY : J = Y
      · exact hbad hField hJY
      · exact step148RankImgGeField_of_ne G A c L h Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ
          hAJ hField hA hJY
  have hXJ : img148 A Y (deltaZero A (lB A) Y) = img148 A Y J :=
    le_antisymm (step148RankImgLe_holds G A c L h Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ
      halt hA) hGe
  have hTen := step148RankTen_of_item134 h133 h134 h48
  have hFT := kf148FieldTypes_holds
  rcases halt with hEq | hTen' | hField
  ·
    have hXK : img148 A Y (deltaZero A (lB A) Y) = img148 A Y K := hXJ.trans hEq.symm
    rcases case148Two_or_of_img148_eq hXK hKY hKΔ hkt with h2 | ⟨hON, htype⟩
    · exact Or.inl h2
    · exact Or.inr (Or.inl (case148Three_of_img148_eq h hXK hP hON htype))
  ·
    obtain ⟨hL7, hW⟩ :=
      hTen G A c L h Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hTen' hA hXJ
    refine Or.inr (Or.inr (Or.inl ⟨?_, hL7, hW⟩))
    rw [hXJ]
    exact hTen'.2
  ·
    have h5 := hFive G A c L h Y hY hs ih hYB B Q e K Le hP hkt he J hJ hKJ hAJ hField hA hXJ
    obtain ⟨n, hn, hKn, hJn, hkind⟩ := hField
    have hKM : K ≤ Y ⊔ A := (hKY.trans inf_le_left).trans le_sup_left
    have : Group.IsPerfect K :=
      isPerfect_of_mem_thetaComponentsIn hP.2.2.2.2.2.1
    have hKp : Group.IsPerfect ↥(img148 A Y K) := isPerfect_img148 hKM
    obtain ⟨hnA7, hnL7, hpf⟩ := hFT _ n hn hKp hKn
    have hLe := hP.2.2.2.2.2.2.2.2.1
    have hLq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hLe
    have : Group.IsPerfect (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) := hLq.1
    have : Nontrivial (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) :=
      CFSG.LocalCores.isQuasisimple_nontrivial hLq
    rcases hkt.2 with ⟨heΩ, hLeA, htype⟩ | ⟨-, htype⟩
    swap
    · exfalso
      rcases htype with ⟨⟨φ⟩⟩ | ⟨h7, ⟨φ⟩⟩
      · exact hnA7.false φ
      · exact (hnL7 h7).false φ
    obtain ⟨m, hm, hLtype⟩ : ∃ m : ℕ, 1 ≤ m ∧
        IsLThreeEpsAt (↥Le ⧸ aschbacherSolvableCore 3 ↥Le) 2 (n * m) := by
      rcases htype with ⟨⟨φ⟩⟩ | ⟨-, ⟨φ⟩⟩ | ⟨p, f, e', hp, hf, he', hLiso, hKiso⟩
      · refine ⟨1, le_rfl, ?_⟩
        rw [mul_one]
        exact isLThreeEpsAt_of_isoLThreePi148 (isoLThreePi_of_mulEquiv148 φ.symm hKn)
      · exact (hnA7.false φ).elim
      · obtain ⟨rfl, rfl⟩ := hpf p f hf hKiso
        exact ⟨e', he', isLThreeEpsAt_of_isoLThreePi148 hLiso⟩
    have hXM : deltaZero A (lB A) Y ≤ Y ⊔ A := (deltaZero_le Y).trans le_sup_left
    refine Or.inr (Or.inr (Or.inr ⟨e, he, Le, n, m, heΩ, hLeA, hn, hm, ?_,
      img148_sup_eq_zpowers hXM he hA hXJ, ?_, ?_, hLtype, h5, K,
        le_inf hP.2.2.2.2.2.2.2.1 (hKY.trans inf_le_left), hKn,
        isPerfect_of_mem_thetaComponentsIn hP.2.2.2.2.2.1, hP.2.2.2.2.2.2.1⟩))
    · rw [hXJ]
      exact hJn
    · rw [hXJ]
      exact not_mem_of_inducesStdKind148 hkind (by decide)
    · rw [hXJ]
      exact hkind

theorem step148Rank_of_res8_kf
    (hKF : KF148SubfieldOver) (h133 : Item133)
    (h134 : Item134) (h48 : Sec4.Item4_8) (hFive : Step148RankFive) : Step148Rank :=
  step148Rank_of_res8 (step148RankImgGeFieldTopDich_of hKF) h133 h134 h48 hFive

end Steps

end Item148Res8

end CFSG.RankThree.PartTwo.Sec14
