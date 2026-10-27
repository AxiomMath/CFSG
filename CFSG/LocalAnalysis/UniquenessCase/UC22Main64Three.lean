module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Main63Three
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2116RParts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

section Reduction

variable {G : Type} [Group G] [Finite G]

structure Steps64Three {G : Type} [Group G] [Finite G] (D : Data G) (Ch : Choice2011 G) :
    Prop where
  s21_6Inf : S21_6Inf D Ch
  s21_13 : S21_13 D Ch
  s21_14 : S21_14 D Ch
  s21_8 : S21_8Sp4 D Ch
  s21_21TB : S21_21TB D Ch
  s22_5_1 : S22_5_1 D Ch
  s21_12 : S21_12 D Ch
  s21_17RJ1 : S21_17RJ1 D Ch
  r8_2 : F08.R82 D
  r8_69N : F08.R869N D
  r8_69M : F08.R869MCons D
  r8_80J4 : F08.R880J4 D
  s21_22R3 : S21_22R3 D Ch
  s21_9Sig3 : S21_9Sig3 D Ch
  s22_fin3R : S22Fin3R D Ch

theorem Steps64Three.toSteps63Three {D : Data G} {Ch : Choice2011 G} (h : Steps64Three D Ch)
    (hCA : CFSG.Open.QTFaithfulEmptyTauCeti.CatalogAgree) : Steps63Three D Ch where
  s21_16R := s21_16R_of_s21_6Inf h.s21_6Inf h.s21_12 h.s21_13 h.s21_14 hCA
  s21_8 := h.s21_8
  s21_21TB := h.s21_21TB
  s22_5_1 := h.s22_5_1
  s21_12 := h.s21_12
  s21_17RJ1 := h.s21_17RJ1
  r8_2 := h.r8_2
  r8_69N := h.r8_69N
  r8_69M := h.r8_69M
  r8_80J4 := h.r8_80J4
  s21_22R3 := h.s21_22R3
  s21_9Sig3 := h.s21_9Sig3
  s22_fin3R := h.s22_fin3R

end Reduction

section Three

variable {G : Type} [Group G] [Finite G]

theorem notTIStage1930_of_steps64Three
    (hS : RankThreeUC.Standing G)
    (hC : RankThreeUC.AGL81TheoremC G)
    (h : ∀ S : RankThreeUC.Setup G, S.InMSigma →
      Steps64Three (PartTwo.Three.dataOfSetup hS S) (fun _ _ => True)) :
    RankThreeUC.NotTIStage1930 G :=
  notTIStage1930_of_steps63Three hS hC fun S hMS =>
    (h S hMS).toSteps63Three CFSG.Open.QTFaithfulEmptyTauCeti.catalogAgree

end Three

end CFSG.LocalAnalysis.UniquenessCase.UC22
