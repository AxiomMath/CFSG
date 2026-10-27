module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSpUSpLabels
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSpUUnitary
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSpUSz
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmega

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGSpULabel (lab : LargeEvenLabel) : Prop :=
  GGSymplecticRecipeLabel lab ∨ GGInndiagUnitaryLabel lab

theorem ggRawFieldConjOn_spU : GGRawFieldConjOn fun _ lab => GGSpULabel lab :=
  ggRawFieldConjOn_symplectic.or ggRawFieldConjOn_unitary

theorem ggRawFieldConjInputExc_of_rest_spU
    (h : GGRawFieldConjOn fun p lab => ¬ (lab.tag = .triD4 ∧ p = 3) ∧
      ¬ GGRawFieldConjDoneLabel lab ∧ ¬ GGOmegaLabel lab ∧ ¬ GGSpULabel lab) :
    GGRawFieldConjInputExc :=
  ggRawFieldConjInputExc_of_rest_omega ((ggRawFieldConjOn_spU.or h).mono
    fun p lab ⟨hne, hd, ho⟩ => by
      by_cases hs : GGSpULabel lab
      · exact Or.inl hs
      · exact Or.inr ⟨hne, hd, ho, hs⟩)

@[expose] def GGRecipeExcConjLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .G2 ∨ lab.tag = .F4 ∨ lab.tag = .E6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨
    lab.tag = .twE6 ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4

theorem ggRecipeExcConjLabel_of_not {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hd : ¬ GGRawFieldConjDoneLabel lab) (ho : ¬ GGOmegaLabel lab) (hs : ¬ GGSpULabel lab) :
    GGRecipeExcConjLabel lab := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨-, hl⟩ := hlab
  simp only [GGRawFieldConjDoneLabel, GGLinearRecipeLabel, GGB2derLabel, GGRecipeSmallExcLabel,
    GGOmegaLabel, GGOmegaPlusLabel, GGOmegaMinusLabel, GGSpULabel, GGSymplecticRecipeLabel,
    GGInndiagUnitaryLabel, GGRecipeExcConjLabel, not_or, not_and] at hd ho hs ⊢
  cases t <;> simp_all <;> omega

theorem ggRawFieldConjInputExc_of_exc
    (h : GGRawFieldConjOn fun p lab => ¬ (lab.tag = .triD4 ∧ p = 3) ∧ GGRecipeExcConjLabel lab) :
    GGRawFieldConjInputExc :=
  ggRawFieldConjInputExc_of_rest_spU fun p hp hp2 lab hlab ⟨hne, hd, ho, hs⟩ =>
    h p hp hp2 lab hlab ⟨hne, ggRecipeExcConjLabel_of_not hlab hd ho hs⟩

theorem twB2_of_not_ggRawFieldCentralDone {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hd : ¬ GGRawFieldCentralDoneLabel lab) (ho : ¬ GGOmegaLabel lab)
    (hs : ¬ GGSymplecticFourLabel lab) : lab.tag = .twB2 := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨-, hl⟩ := hlab
  simp only [GGRawFieldCentralDoneLabel, GGLinearRecipeLabel, GGSymplecticHighLabel, GGB2derLabel,
    GGRecipeSmallExcLabel, GGRecipeOutCyclicLabel, GGRecipeExcOutLabel, GGInndiagUnitaryLabel,
    GGRecipeE6Label, GGRecipeTwE6Label, GGOmegaLabel, GGOmegaPlusLabel, GGOmegaMinusLabel,
    GGSymplecticFourLabel, not_or, not_and] at hd ho hs ⊢
  cases t <;> simp_all <;> omega


theorem ggRawFieldCentralInput_of_rest_spU (hT : PlusFourTrialityInput)
    (h : GGRawFieldCentralOn fun lab => ¬ GGRawFieldCentralDoneLabel lab ∧ ¬ GGOmegaLabel lab ∧
      ¬ GGSymplecticFourLabel lab) :
    GGRawFieldCentralInput :=
  ggRawFieldCentralInput_of_rest_omega hT ((ggRawFieldCentralOn_symplecticFour.or h).mono
    fun lab ⟨hd, ho⟩ => by
      by_cases hs : GGSymplecticFourLabel lab
      · exact Or.inl hs
      · exact Or.inr ⟨hd, ho, hs⟩)

theorem ggRawFieldCentralInput_of_twB2 (hT : PlusFourTrialityInput)
    (h : GGRawFieldCentralOn fun lab => lab.tag = .twB2) : GGRawFieldCentralInput :=
  ggRawFieldCentralInput_of_rest_spU hT fun lab hlab ⟨hd, ho, hs⟩ =>
    h lab hlab (twB2_of_not_ggRawFieldCentralDone hlab hd ho hs)

theorem ggRawFieldCentralInput_of_triality (hT : PlusFourTrialityInput) : GGRawFieldCentralInput :=
  ggRawFieldCentralInput_of_twB2 hT ggRawFieldCentralOn_twB2

end CFSG.StandardType
