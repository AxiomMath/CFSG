module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKSmallDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKSmallChainExc
public import CFSG.LocalAnalysis.StandardType.GGSixRCKSmallChainTri
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265CDynO2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265CDynE2
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzTower.Rest
public import CFSG.HardMathSupport.Lang.Coordinator.OuterFixedOrderE6Order
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneFieldRoot
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HG2InnMain
public import CFSG.LocalAnalysis.RankThreeTheoremC.RelativePairInputs
public import CFSG.RankThree.PartOne.KF.F128Count
public import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoSporadicOpen

public section

namespace CFSG.StandardType.RCKSmall

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.Y10GField
open CFSG.LocalAnalysis.GLTheoremA.S265C.DynE (TagLieType IsADETag tagLie_twE6)
open CFSG.LocalAnalysis.GLTheoremA.S265C.DynO

theorem compTypeLie2Small_holds :
    CompTypeLie2Small := by
  intro S _ _ labL β p hp hp2 hcen hin hβp hβ1 hG2 hB2der hG2der htwF4der htwB2 htwF4 J hJ
  have hcls : ClassicalOr360 ↥J → TagLieType (fun t => ¬ RCKSmallLieTag t) 2 ↥J ∨
      Nat.card (↥J ⧸ Subgroup.center ↥J) = 360 := by
    rintro (⟨t, r, e, ht, hm⟩ | h)
    · exact Or.inl ⟨t, r, e, by rcases ht with rfl | rfl | rfl | rfl | rfl <;> simp [RCKSmallLieTag],
        hm⟩
    · obtain ⟨e⟩ := h
      exact Or.inr (by
        rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
          Fintype.card_fin]
        decide)
  have hade : ∀ t, IsADETag t ∨ t = .trialityD4 → ¬ RCKSmallLieTag t := by
    intro t ht
    rcases ht with ht | rfl
    · unfold IsADETag at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [RCKSmallLieTag]
    · simp [RCKSmallLieTag]
  rcases fam_cover labL with hF | hF | hF | hF | hF
  · exact hcls (classicalOr360_lin hp hp2 hcen hF hin hβp hJ)
  · exact hcls (classicalOr360_uni hp hp2 hcen hF hin hβp hJ)
  · rcases hF with hB | hCt | hB2
    · exact hcls (classicalOr360_symp hp hp2 hcen (Or.inl hB) hin hβp hJ)
    · exact hcls (classicalOr360_symp hp hp2 hcen (Or.inr hCt) hin hβp hJ)
    · exact (hB2der hB2).elim
  · exact hcls (classicalOr360_orth hp hp2 hcen hF hin hβp hJ)
  · rcases hF with hE6 | hE7 | hE8 | hF4 | htwE6 | htriD4 | hG2c | hG2derc | htwB2c | htwF4c |
      htwF4derc
    · exact Or.inl ((rck_tagLie_E hp hp2 hcen hin hβp hβ1 (Or.inl hE6) hJ).mono hade)
    · exact Or.inl ((rck_tagLie_E hp hp2 hcen hin hβp hβ1 (Or.inr (Or.inl hE7)) hJ).mono hade)
    · exact Or.inl ((rck_tagLie_E hp hp2 hcen hin hβp hβ1 (Or.inr (Or.inr hE8)) hJ).mono hade)
    · exact hcls (classicalOr360_F4 hp hp2 hcen hin hβp hβ1 hF4 hJ)
    · exact Or.inl ((tagLie_twE6 hp hp2 hcen hin hβp hβ1 htwE6 hJ).mono hade)
    · exact Or.inl ((rck_tagLie_triD4 hp hp2 hcen hin hβp hβ1 htriD4 hJ).mono fun t ht => by
        rcases ht with rfl | rfl <;> simp [RCKSmallLieTag])
    · exact (hG2 hG2c).elim
    · exact (hG2der hG2derc).elim
    · exact (htwB2 htwB2c).elim
    · exact (htwF4 htwF4c).elim
    · exact (htwF4der htwF4derc).elim

end CFSG.StandardType.RCKSmall
