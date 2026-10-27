module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIBPSL
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIBOmegaPlus
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIBOmegaMinus
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIBE6
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIBE7
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIBE8
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIBF4
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIBTwE6
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2PSLInner
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2PSLCores
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaForms
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaCores
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2E6Root
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongE6
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2E7Root
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongE7
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2E8Inner
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongE8
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2F4Inner
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongF4
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6Root
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongTwE6

public section

namespace CFSG.StandardType.RCKK1II

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.Open

theorem rckRowIIAt_PSL
    (n : ℕ) (hn : 5 ≤ n) (hadm : StatedLieAdmissible .PSL n 2 1) : RCKRowIIAt .PSL n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact rckRowIIAt_of_pair .PSL (m + 1) (by simp [GGPosTag]) hadm
    (fun X _ _ φ hker β hβ _ u =>
      CFSG.StandardType.LieKnownR2.PSL.ggRootInnerAt_ggU_psl (m := m) (g := 1)
        (Or.inl ⟨rfl, by omega⟩) φ hker hβ u)
    (fun β hβ _ u Rr Q hRr hQ =>
      (CFSG.StandardType.LieKnownR2.PSL.coreFour_PSL (m := m) (f := 1) hβ u hRr hQ).1)
    (rckIIPair_PSL (m + 1) hn hadm)

theorem rckRowIIAt_OmegaPlus
    (n : ℕ) (hn : 4 ≤ n) (hadm : StatedLieAdmissible .POmegaPlus n 2 1) :
    RCKRowIIAt .POmegaPlus n :=
  rckRowIIAt_of_pair .POmegaPlus n (by simp [GGPosTag]) hadm
    (fun X _ _ φ hker β hβ _ u =>
      CFSG.StandardType.LieKnownR2.POmega.ggRootInnerAt_ggU_pomegaPlus hn φ hker hβ u)
    (fun β _ hl u Rr Q hRr hQ =>
      (CFSG.StandardType.LieKnownR2.POmega.coreFour_POmegaPlus_long hn hl u hRr hQ).1)
    (rckIIPair_OmegaPlus n hn hadm)

theorem rckRowIIAt_OmegaMinus
    (n : ℕ) (hn : 4 ≤ n) (hadm : StatedLieAdmissible .POmegaMinus n 2 1) :
    RCKRowIIAt .POmegaMinus n :=
  rckRowIIAt_of_pair .POmegaMinus n (by simp [GGPosTag]) hadm
    (fun X _ _ φ hker β hβ hl u =>
      CFSG.StandardType.LieKnownR2.POmega.ggRootInnerAt_ggU_pomegaMinus hn φ hker hβ hl u)
    (fun β _ hl u Rr Q hRr hQ =>
      (CFSG.StandardType.LieKnownR2.POmega.coreFour_POmegaMinus_long hn hl u hRr hQ).1)
    (rckIIPair_OmegaMinus n hn hadm)

theorem rckRowIIAt_E6
    (n : ℕ) (hadm : StatedLieAdmissible .E6 n 2 1) : RCKRowIIAt .E6 n :=
  rckRowIIAt_of_pair .E6 n (by simp [GGPosTag]) hadm
    (fun X _ _ φ hker β hβ _ u =>
      CFSG.StandardType.LieKnownR2.E6.ggRootInnerAt_ggU_e6 le_rfl φ hker hβ u)
    (fun β hβ _ u Rr Q hRr hQ => (CFSG.StandardType.LieKnownR2.E6.coreFour_E6 hβ u hRr hQ).1)
    (rckIIPair_E6 n hadm)

theorem rckRowIIAt_E7
    (n : ℕ) (hadm : StatedLieAdmissible .E7 n 2 1) : RCKRowIIAt .E7 n :=
  rckRowIIAt_of_pair .E7 n (by simp [GGPosTag]) hadm
    (fun X _ _ φ hker β hβ _ u =>
      CFSG.StandardType.LieKnownR2.E7.ggRootInnerAt_ggU_e7 le_rfl φ hker hβ u)
    (fun β hβ _ u Rr Q hRr hQ => (CFSG.StandardType.LieKnownR2.E7.coreFour_E7 hβ u hRr hQ).1)
    (rckIIPair_E7 n hadm)

theorem rckRowIIAt_E8
    (n : ℕ) (hadm : StatedLieAdmissible .E8 n 2 1) : RCKRowIIAt .E8 n :=
  rckRowIIAt_of_pair .E8 n (by simp [GGPosTag]) hadm
    (fun X _ _ φ hker β hβ _ u =>
      CFSG.StandardType.LieKnownR2.E8.ggRootInnerAt_ggU_e8 le_rfl φ hker hβ u)
    (fun β hβ _ u Rr Q hRr hQ => (CFSG.StandardType.LieKnownR2.E8.coreFour_E8 hβ u hRr hQ).1)
    (rckIIPair_E8 n hadm)

theorem rckRowIIAt_F4
    (n : ℕ) (hadm : StatedLieAdmissible .F4 n 2 1) : RCKRowIIAt .F4 n :=
  rckRowIIAt_of_pair .F4 n (by simp [GGPosTag]) hadm
    (fun X _ _ φ hker β hβ _ u =>
      CFSG.StandardType.LieKnownR2.F4.ggRootInnerAt_ggU_f4 le_rfl φ hker hβ u)
    (fun β _ hl u Rr Q hRr hQ =>
      (CFSG.StandardType.LieKnownR2.Short.coreFour_F4_long hl u hRr hQ).1)
    (rckIIPair_F4 n hadm)

theorem rckRowIIAt_TwE6
    (n : ℕ) (hadm : StatedLieAdmissible .twistedE6 n 2 1) : RCKRowIIAt .twistedE6 n :=
  rckRowIIAt_of_pair .twistedE6 n (by simp [GGPosTag]) hadm
    (fun X _ _ φ hker β _ hl u =>
      CFSG.StandardType.LieKnownR2.TwE6.ggRootInnerAt_ggU_twistedE6_long le_rfl φ hker hl u)
    (fun β _ hl u Rr Q hRr hQ =>
      (CFSG.StandardType.LieKnownR2.Short.coreFour_twistedE6_long le_rfl hl u hRr hQ).1)
    (rckIIPair_TwE6 n hadm)

end CFSG.StandardType.RCKK1II
