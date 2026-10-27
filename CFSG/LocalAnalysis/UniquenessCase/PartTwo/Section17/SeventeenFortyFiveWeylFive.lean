module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveWeylFiveOut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveWeylFiveExc
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveWeylFiveLinear
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveWeylFiveUnitary
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveWeylFiveSymplectic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveWeylFiveOrthogonal
import CFSG.Adapters.TauCetiLieModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

theorem weylFivePower_of_smallWeyl
    (d : TauCeti.ValidLieTypeIndex) (hd : SmallWeylIndex45 d.1)
    (h2 : d.1.characteristic ≠ 2) (h31 : d.1.characteristic ≠ 31) :
    WeylFivePower (TauCeti.CFSGIndex.lie d).Group := by
  obtain ⟨i, hi⟩ := d
  cases i with
  | A n q =>
    simp only [SmallWeylIndex45] at hd
    have hq2 : q.p ≠ 2 := by simpa using h2
    have hq31 : q.p ≠ 31 := by simpa using h31
    obtain ⟨-, hSC | ⟨h0, -⟩⟩ :=
      CFSG.Models.lieModel_A (G := (TauCeti.CFSGIndex.lie ⟨.A n q, hi⟩).Group) n q hi
        (MulEquiv.refl _)
    · exact weylFivePower_of_model_PSL hSC (by omega) hq2 hq31
    · omega
  | twistedA n q =>
    simp only [SmallWeylIndex45] at hd
    have hq2 : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA n q, hi⟩ ≠ 2 := by
      change (TauCeti.LieTypeIndex.twistedA n q).characteristic ≠ 2
      simpa using h2
    have hq31 : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA n q, hi⟩ ≠ 31 := by
      change (TauCeti.LieTypeIndex.twistedA n q).characteristic ≠ 31
      simpa using h31
    obtain ⟨-, hSC | ⟨h0, -⟩⟩ :=
      CFSG.Models.lieModel_twistedA (G := (TauCeti.CFSGIndex.lie ⟨.twistedA n q, hi⟩).Group)
        n q hi (MulEquiv.refl _)
    · exact weylFivePower_of_model_PSU hSC (by omega) hq2 hq31
    · omega
  | B n q =>
    simp only [SmallWeylIndex45] at hd
    have hq2 : q.p ≠ 2 := by simpa using h2
    have hq31 : q.p ≠ 31 := by simpa using h31
    rcases CFSG.Models.lieModel_B (G := (TauCeti.CFSGIndex.lie ⟨.B n q, hi⟩).Group) n q hi
      (MulEquiv.refl _) with hm | hm
    · obtain ⟨hadm, hSC | ⟨h0, -⟩⟩ := hm
      · exact weylFivePower_of_model_PSp hSC hd hq2 hq31
      · have := hadm.2.2.1; omega
    · obtain ⟨hadm, hSC | ⟨h0, -⟩⟩ := hm
      · exact weylFivePower_of_model_POmegaOdd hSC hd hq2 hq31
      · have := hadm.2.2.1; omega
  | C n q =>
    simp only [SmallWeylIndex45] at hd
    have hq2 : q.p ≠ 2 := by simpa using h2
    have hq31 : q.p ≠ 31 := by simpa using h31
    obtain ⟨hadm, hSC | ⟨h0, -⟩⟩ :=
      CFSG.Models.lieModel_C (G := (TauCeti.CFSGIndex.lie ⟨.C n q, hi⟩).Group) n q hi
        (MulEquiv.refl _)
    · exact weylFivePower_of_model_PSp hSC hd hq2 hq31
    · have := hadm.2.2.1; omega
  | D n q =>
    simp only [SmallWeylIndex45] at hd
    have hq2 : q.p ≠ 2 := by simpa using h2
    have hq31 : q.p ≠ 31 := by simpa using h31
    obtain ⟨hadm, hSC | ⟨h0, -⟩⟩ :=
      CFSG.Models.lieModel_D (G := (TauCeti.CFSGIndex.lie ⟨.D n q, hi⟩).Group) n q hi
        (MulEquiv.refl _)
    · obtain rfl : n = 4 := by have := hadm.2.2; omega
      exact weylFivePower_of_model_POmegaPlus_four hSC hq31
    · have := hadm.2.2; omega
  | twistedD n q =>
    simp only [SmallWeylIndex45] at hd
    have hq2 : q.p ≠ 2 := by simpa using h2
    have hq31 : q.p ≠ 31 := by simpa using h31
    obtain ⟨hadm, hSC | ⟨h0, -⟩⟩ :=
      CFSG.Models.lieModel_twistedD (G := (TauCeti.CFSGIndex.lie ⟨.twistedD n q, hi⟩).Group)
        n q hi (MulEquiv.refl _)
    · exact weylFivePower_of_model_POmegaMinus hSC hd hq2 hq31
    · have := hadm.2.2; omega
  | G2 q =>
    simp only [SmallWeylIndex45] at hd
    have hq2 : q.p ≠ 2 := by simpa using h2
    have hq31 : q.p ≠ 31 := by simpa using h31
    exact weylFivePower_G2 hi hq2 hq31
  | F4 q =>
    simp only [SmallWeylIndex45] at hd
    have hq2 : q.p ≠ 2 := by simpa using h2
    have hq31 : q.p ≠ 31 := by simpa using h31
    exact weylFivePower_F4 hi hq2 hq31
  | trialityD4 q =>
    simp only [SmallWeylIndex45] at hd
    have hq2 : q.p ≠ 2 := by simpa using h2
    have hq31 : q.p ≠ 31 := by simpa using h31
    exact weylFivePower_trialityD4 hi hq2 hq31
  | E6 q => exact absurd hd (by simp [SmallWeylIndex45])
  | E7 q => exact absurd hd (by simp [SmallWeylIndex45])
  | E8 q => exact absurd hd (by simp [SmallWeylIndex45])
  | twistedE6 q => exact absurd hd (by simp [SmallWeylIndex45])
  | suzuki m => exact absurd hd (by simp [SmallWeylIndex45])
  | reeG2 m => exact absurd hd (by simp [SmallWeylIndex45])
  | reeF4 m => exact absurd hd (by simp [SmallWeylIndex45])
  | tits => exact absurd hd (by simp [SmallWeylIndex45])

theorem k45WeylFive_holds :
    K45WeylFive :=
  k45WeylFive_of_types fun d hd h2 h31 =>
    ⟨weylFiveInner_of_smallWeyl d hd h2, weylFivePower_of_smallWeyl d hd h2 h31⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
