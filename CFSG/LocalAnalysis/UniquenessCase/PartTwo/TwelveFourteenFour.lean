module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveFourteenSetupAS
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSevenBAS

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)

variable {G : Type} [Group G] [Finite G]

theorem r126_four_of_AS
    (h5_11 : WeakClosure81.Asch5_11AS) (h5_13 : WeakClosure81.Asch5_13AS) :
    ∀ (G : Type) [Group G] [Finite G] (hS : Standing4 G) (hU : uniqueFourUnique G)
      (S : Setup4 G), S.InMSigma → PartIAt S.M → R126 (UC6.dataOfSetup4 hS hU S) :=
  fun _ _ _ hS hU S hMS hPart =>
    WeakClosure81.r126_of_twelve_six_AS _ h5_11 h5_13
      (UC6.r6_6_dataOfSetup4 hS hU S hMS hPart.1)

theorem r127_four_of_AS
    (h5_11 : WeakClosure81.Asch5_11AS) (h5_13 : WeakClosure81.Asch5_13AS)
    (h861 : ∀ (G : Type) [Group G] [Finite G], W3Lem86_1 G)
    (h88 : ∀ (G : Type) [Group G] [Finite G], W3Thm88 G)
    (h93 : ∀ (G : Type) [Group G] [Finite G] (V T : Subgroup G), WeakClosure81.Thm93Syl V T)
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement) :
    ∀ (G : Type) [Group G] [Finite G] (hS : Standing4 G) (hU : uniqueFourUnique G)
      (S : Setup4 G), S.InMSigma → PartIAt S.M → R127 (UC6.dataOfSetup4 hS hU S) :=
  fun G _ _ hS hU S hMS hPart =>
    r127_of_twelve_seven_AS_syl hTim S.notCatalog _ h5_11 h5_13
      (UC6.r6_3_dataOfSetup4 hS hU S hPart.1) (UC6.r6_6_dataOfSetup4 hS hU S hMS hPart.1)
      (h861 G) (h88 G) fun V => h93 G V _

theorem r1214_four_of_AS
    (h5_11 : WeakClosure81.Asch5_11AS) (h5_13 : WeakClosure81.Asch5_13AS)
    (h861 : ∀ (G : Type) [Group G] [Finite G], W3Lem86_1 G)
    (h88 : ∀ (G : Type) [Group G] [Finite G], W3Thm88 G)
    (h93 : ∀ (G : Type) [Group G] [Finite G] (V T : Subgroup G), WeakClosure81.Thm93Syl V T)
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement) :
    ∀ (G : Type) [Group G] [Finite G] (hS : Standing4 G) (hU : uniqueFourUnique G)
      (S : Setup4 G), S.InMSigma → PartIAt S.M → F12.R1214 (UC6.dataOfSetup4 hS hU S) :=
  fun G _ _ hS hU S hMS hPart =>
    r1214_ofSetup4_AS hS hU S hMS hPart.1 h5_11 h5_13
      (r127_four_of_AS h5_11 h5_13 h861 h88 h93 hTim G hS hU S hMS hPart)
      (h861 G) hTim

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
