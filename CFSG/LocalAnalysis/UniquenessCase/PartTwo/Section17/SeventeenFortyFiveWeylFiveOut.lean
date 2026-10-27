module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveWeylFiveDFour
import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.PSL2Odd
import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieOutCycClassical
import CFSG.RankThree.PartOne.MB3.OddOutLinear

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

private theorem not_dvd_gcd_of_le_four {m N : ℕ} (hm1 : 1 ≤ m) (hm4 : m ≤ 4) :
    ¬ 31 ∣ Nat.gcd m N := by
  intro hdvd
  have hpos : 0 < Nat.gcd m N := Nat.gcd_pos_of_pos_left N (by omega)
  have hle : Nat.gcd m N ≤ m := Nat.gcd_le_left N (by omega)
  have := Nat.le_of_dvd hpos hdvd
  omega

theorem weylFiveInner_of_smallWeyl
    (d : TauCeti.ValidLieTypeIndex) (hd : SmallWeylIndex45 d.1)
    (h2 : d.1.characteristic ≠ 2) : WeylFiveInner (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨i, hi⟩ := d
  cases i with
  | A n q =>
    simp only [SmallWeylIndex45] at hd
    have hq2 : q.p ≠ 2 := by simpa using h2
    obtain ⟨hadm, hSC | ⟨h0, -⟩⟩ :=
      CFSG.Models.lieModel_A (G := (TauCeti.CFSGIndex.lie ⟨.A n q, hi⟩).Group) n q hi
        (MulEquiv.refl _)
    · by_cases hn1 : n = 1
      · subst hn1
        exact weylFiveInner_of_outPNice
          (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.outPNice_PSL_two_odd_all
            (p := 31) (by norm_num) (by norm_num) hq2 hSC)
      · have hn2 : 2 ≤ n := by have := hadm.2.2.1; omega
        exact weylFiveInner_of_outPNice
          (CFSG.RankThree.PartOne.OutStructure.outPNice_PSL_ge_three_odd
            (p := 31) (by norm_num) (by norm_num) (by omega) hSC
            (not_dvd_gcd_of_le_four (by omega) (by omega)))
    · omega
  | twistedA n q =>
    simp only [SmallWeylIndex45] at hd
    obtain ⟨hadm, hSC | ⟨h0, -⟩⟩ :=
      CFSG.Models.lieModel_twistedA (G := (TauCeti.CFSGIndex.lie ⟨.twistedA n q, hi⟩).Group)
        n q hi (MulEquiv.refl _)
    · exact weylFiveInner_of_outPNice
        (CFSG.RankThree.PartOne.OutStructure.outPNice_PSU_odd
          (p := 31) (by norm_num) hSC (not_dvd_gcd_of_le_four (by omega) (by omega)))
    · have := hadm.2.2.1; omega
  | B n q =>
    simp only [SmallWeylIndex45] at hd
    rcases CFSG.Models.lieModel_B (G := (TauCeti.CFSGIndex.lie ⟨.B n q, hi⟩).Group) n q hi
      (MulEquiv.refl _) with hm | hm
    · obtain ⟨hadm, hSC | ⟨h0, -⟩⟩ := hm
      · exact weylFiveInner_of_outPNice
          (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.outPNice_statedClassicalModel_PSp
            (p := 31) (by norm_num) (by norm_num) hadm.2.2.1 hSC)
      · have := hadm.2.2.1; omega
    · obtain ⟨hadm, hSC | ⟨h0, -⟩⟩ := hm
      · exact weylFiveInner_of_outPNice
          (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.outPNice_POmegaOdd_all
            (p := 31) (by norm_num) (by norm_num) hSC)
      · have := hadm.2.2.1; omega
  | C n q =>
    simp only [SmallWeylIndex45] at hd
    obtain ⟨hadm, hSC | ⟨h0, -⟩⟩ :=
      CFSG.Models.lieModel_C (G := (TauCeti.CFSGIndex.lie ⟨.C n q, hi⟩).Group) n q hi
        (MulEquiv.refl _)
    · exact weylFiveInner_of_outPNice
        (CFSG.LocalAnalysis.GLTheoremA.KD264Lie.outPNice_statedClassicalModel_PSp
          (p := 31) (by norm_num) (by norm_num) hadm.2.2.1 hSC)
    · have := hadm.2.2.1; omega
  | D n q =>
    simp only [SmallWeylIndex45] at hd
    have hq2 : q.p ≠ 2 := by simpa using h2
    obtain ⟨hadm, hSC | ⟨h0, -⟩⟩ :=
      CFSG.Models.lieModel_D (G := (TauCeti.CFSGIndex.lie ⟨.D n q, hi⟩).Group) n q hi
        (MulEquiv.refl _)
    · obtain rfl : n = 4 := by have := hadm.2.2; omega
      exact weylFiveInner_of_model_POmegaPlus_four hSC
    · have := hadm.2.2; omega
  | twistedD n q =>
    simp only [SmallWeylIndex45] at hd
    obtain ⟨hadm, hSC | ⟨h0, -⟩⟩ :=
      CFSG.Models.lieModel_twistedD (G := (TauCeti.CFSGIndex.lie ⟨.twistedD n q, hi⟩).Group)
        n q hi (MulEquiv.refl _)
    · exact weylFiveInner_of_outPNice
        (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.outPNice_POmegaMinus_all
          (p := 31) (by norm_num) (by norm_num) hSC)
    · have := hadm.2.2; omega
  | G2 q =>
    simp only [SmallWeylIndex45] at hd
    have hq2 : q.p ≠ 2 := by simpa using h2
    have hq3 : 3 ≤ q.p ^ q.exponent := by
      rw [← TauCeti.PrimePower.card_def]
      exact (TauCeti.LieTypeIndex.inStandardRange_iff (.G2 q)).1
        ((TauCeti.LieTypeIndex.valid_iff (.G2 q)).1 hi).1
    have hm : CFSG.Blueprint.ChevalleyExceptionalModel
        (TauCeti.CFSGIndex.lie ⟨.G2 q, hi⟩).Group .G2 q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl, hq3⟩,
        CFSG.TauCetiBridge.untwistedModel_of_bridge
          CFSG.TauCetiBridge.chevalleyBridges.g2 q hi hq2 (MulEquiv.refl _)⟩
    by_cases h3 : q.p = 3
    · rw [h3] at hm
      exact weylFiveInner_of_outPNice
        (CFSG.RankThree.PartOne.OutStructure.outPNice_G2_three (p := 31) (by norm_num) hm)
    · exact weylFiveInner_of_outPNice
        (CFSG.RankThree.PartOne.OutStructure.outPNice_G2_odd
          (p := 31) (by norm_num) hq2 h3 hm)
  | F4 q =>
    simp only [SmallWeylIndex45] at hd
    have hq2 : q.p ≠ 2 := by simpa using h2
    have hm : CFSG.Blueprint.ChevalleyExceptionalModel
        (TauCeti.CFSGIndex.lie ⟨.F4 q, hi⟩).Group .F4 q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
        CFSG.TauCetiBridge.untwistedModel_of_bridge
          CFSG.TauCetiBridge.chevalleyBridges.f4 q hi hq2 (MulEquiv.refl _)⟩
    exact weylFiveInner_of_outPNice
      (CFSG.RankThree.PartOne.OutStructure.outPNice_F4_odd (p := 31) (by norm_num) hq2 hm)
  | trialityD4 q =>
    simp only [SmallWeylIndex45] at hd
    have hq2 : q.p ≠ 2 := by simpa using h2
    have hm : CFSG.Blueprint.ChevalleyExceptionalModel
        (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hi⟩).Group .trialityD4 q.p q.exponent :=
      ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
        CFSG.TauCetiBridge.twistedModel_of_bridge
          CFSG.TauCetiBridge.chevalleyBridges.trialityD4 q hi hq2
          (by decide : 0 < CFSG.Blueprint.Chevalley.TwistTag.D4.order) (MulEquiv.refl _)⟩
    exact weylFiveInner_of_outPNice
      (CFSG.RankThree.PartOne.OutStructure.outPNice_trialityD4_odd
        (p := 31) (by norm_num) hq2 hm)
  | E6 q => exact absurd hd (by simp [SmallWeylIndex45])
  | E7 q => exact absurd hd (by simp [SmallWeylIndex45])
  | E8 q => exact absurd hd (by simp [SmallWeylIndex45])
  | twistedE6 q => exact absurd hd (by simp [SmallWeylIndex45])
  | suzuki m => exact absurd hd (by simp [SmallWeylIndex45])
  | reeG2 m => exact absurd hd (by simp [SmallWeylIndex45])
  | reeF4 m => exact absurd hd (by simp [SmallWeylIndex45])
  | tits => exact absurd hd (by simp [SmallWeylIndex45])

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
