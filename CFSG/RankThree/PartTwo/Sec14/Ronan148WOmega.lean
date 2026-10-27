module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.Step148M24Hbar
public import CFSG.RankThree.PartTwo.Sec14.Ronan148WCase1
public import CFSG.RankThree.PartTwo.Sec14.Ronan148WOmega134
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec15.Item152ResProofW

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec14.Main148 CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.Step148M24



theorem sec13HJPointOmega_of (h134 : Item134) (h48 : Sec4.Item4_8) : Sec13HJPointOmega := by
  intro G _ _ A c L hStd Y hY hs ih B hB hnot YB hYB htype hΔ b d Lb hc hle J hJ hYBJ hAJ Yd hYd
    hYBYd hYdJ hAYd hA6 hθ hW hdc hYB6 hdYB hb hM a haB ha1 ha3 haC
  have hker : (ker148 A Y).Normal := ker148_normal hY.2
  obtain ⟨e⟩ := hM
  have hA : Late.IsE27 A := hStd.isE27
  have hA3 : ∀ x ∈ A, x ^ 3 = 1 := hA.1.2
  have hdYd : d ∈ Yd := hYBYd hdYB
  obtain ⟨hbB, hdB, hb1, hd1, -⟩ := lbConfig_points hB hA.2 hc
  have hdA : d ∈ A := hB.1 hdB
  have hbA : b ∈ A := hB.1 hbB
  rcases omega_cases_of_lbConfig h134 h48 hStd hB hc with hΩ1 | ⟨hpts, hHJ⟩
  ·
    have hab := zpowers_eq_of_omegaA_eq_singleton hStd hY.2 hB hc hJ hAJ hYd hYdJ hA6 hθ hdc hdYd
      e hΩ1 haB ha1 haC
    refine ⟨hab ▸ hc.2.1, Lb, ?_, Item148HJ.j2_of_isLBConfig hc⟩
    rw [Sec13.lA_congr hab]
    exact hc.2.2.1 ▸ Set.mem_singleton Lb
  ·
    have hAN : A ≤ Subgroup.normalizer (pPrimeCoreOf 3 Y : Set G) :=
      hY.2.trans (normalizer_le_normalizer_pPrimeCoreOf 3 Y)
    have haS : a ∈ sectionCentralizerSubgroup148 A J (pPrimeCoreOf 3 Y) hAJ hAN := haC
    have hda : d ∉ Subgroup.zpowers a := fun h => hdc ((Subgroup.zpowers_le.mpr haS) h)
    have hB9 : Nat.card B = 9 := by
      have h27 : Nat.card A = 27 := hA.2
      have h9 : 3 * Nat.card B = 27 := by rw [← hB.2, h27]
      omega
    have hd3 : Nat.card (Subgroup.zpowers d) = 3 :=
      Sec13.card_zpowers_of_pow_three (hA3 d hdA) hd1
    have hbd : b ∉ Subgroup.zpowers d := by
      intro h
      have hBle : B ≤ Subgroup.zpowers d := by
        rw [hc.1, Subgroup.closure_le]
        intro z hz
        rcases hz with rfl | hz
        · exact h
        · rw [Set.mem_singleton_iff] at hz
          rw [hz]
          exact Subgroup.mem_zpowers d
      have := Subgroup.card_le_of_le hBle
      rw [hB9, hd3] at this
      omega
    have hcl : B = Subgroup.zpowers b ⊔ Subgroup.zpowers d := by
      rw [hc.1, Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
        ← Subgroup.zpowers_eq_closure]
    have ha3' : Nat.card (Subgroup.zpowers a) = 3 := Sec13.card_zpowers_of_pow_three ha3 ha1
    have had : Subgroup.zpowers a ≠ Subgroup.zpowers d := fun h =>
      hda (h ▸ Subgroup.mem_zpowers d)
    obtain ⟨f, hf, haf⟩ := Sec15.Proof152ResW.exists_eq_zpowers_mul hA hbA hdA hd1 hbd
      (hcl ▸ Subgroup.zpowers_le.mpr haB) ha3' had
    have haΩ : Subgroup.zpowers a ∈ omegaA A := haf ▸ hpts f hf
    obtain ⟨x, hx, Lx, hLx, hj⟩ := hHJ _ haΩ
    exact ⟨haΩ, Lx, (Sec13.lA_congr hx) ▸ hLx, hj⟩

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
