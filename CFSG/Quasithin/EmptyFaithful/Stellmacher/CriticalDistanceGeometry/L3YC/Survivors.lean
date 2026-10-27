module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.L3YC.L32Row
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.L3YC.ModO2Iso
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmall
public import CFSG.RankThree.PartTwo.Sec4.LThreePiKind
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.EmptyFaithful.S153DInputs

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace Stellmacher.CD.L3YC

section Bridge

variable {G : Type} [Group G]

theorem isPSL_modO2_modO2Image {H L : Subgroup G} (hLH : L ≤ H) (hq : IsLnTwoQuot L 3) :
    IsPSL 3 2 1 (ModO2 (modO2Image H L)) := by
  obtain ⟨e1⟩ := modO2_modO2Image_equiv hLH
  obtain ⟨e2⟩ := hq
  have hK : Nat.card (ZMod 2) = 2 := by simp
  refine ⟨by norm_num [CFSG.Assembly.LowTwoRank.StatedLieAdmissible], ZMod 2, inferInstance,
    inferInstance, by simp, ⟨(e1.trans e2).trans
      (((CFSG.RankThree.PartTwo.Sec4.statedSLEquiv 3 (ZMod 2)).trans
        (CFSG.QuasithinUnique.Setup.Family.statedProjSL_equiv_of_card_two 3 (ZMod 2) hK).symm))⟩⟩

end Bridge

theorem survivor_of_rows {G : Type} [Group G] [Finite G]
    {H L L₁ : Subgroup G} (hLH : L ≤ H) (hLL₁ : L ≤ L₁) (hq : IsLnTwoQuot L 3)
    (h : A312Case (modO2Image H L) (modO2Image H L₁) ∨
      A312Nonquasi (modO2Image H L) (modO2Image H L₁)) :
    L32.L32Survivor (modO2Image H L) (modO2Image H L₁) ∨
      (⁅(CFSG.oddCore ↥(modO2Image H L₁)).map (modO2Image H L₁).subtype,
          modO2Image H L₁⁆ ≠ ⊥ ∧
        modO2Image H L₁ = modO2Image H L ⊔
          (CFSG.oddCore ↥(modO2Image H L₁)).map (modO2Image H L₁).subtype ∧
        IsSL2 7 (↥(modO2Image H L₁) ⧸ CFSG.oddCore ↥(modO2Image H L₁)) ∧
        Nat.card ↥(modO2Image H L) = 336) :=
  L32.row_of_a312_l32 (Subgroup.map_mono fun _ hx => hLL₁ hx) (isPSL_modO2_modO2Image hLH hq) h

end Stellmacher.CD.L3YC

end CFSG.Quasithin
