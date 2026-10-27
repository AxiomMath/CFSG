module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclicLabels
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldUnitary
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldLinearLang
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcInn
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldE6

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGRawFieldConjDoneLabel (lab : LargeEvenLabel) : Prop :=
  GGLinearRecipeLabel lab ∨ GGB2derLabel lab ∨ GGRecipeSmallExcLabel lab

theorem ggRawFieldConjInputExc_of_rest
    (h : GGRawFieldConjOn fun p lab => ¬ (lab.tag = .triD4 ∧ p = 3) ∧
      ¬ GGRawFieldConjDoneLabel lab) :
    GGRawFieldConjInputExc := by
  refine ggRawFieldConjInputExc_of_on (S := fun p lab => GGRawFieldConjDoneLabel lab ∨
      (¬ (lab.tag = .triD4 ∧ p = 3) ∧ ¬ GGRawFieldConjDoneLabel lab))
    (fun p lab _ hne => by tauto) ?_
  exact (ggRawFieldConjOn_linear.or (ggRawFieldConjOn_b2der.or ggRawFieldConjOn_smallExc)).or h

@[expose] def GGRawFieldCentralDoneLabel (lab : LargeEvenLabel) : Prop :=
  GGLinearRecipeLabel lab ∨ GGSymplecticHighLabel lab ∨ GGB2derLabel lab ∨
    GGRecipeSmallExcLabel lab ∨ GGRecipeOutCyclicLabel lab ∨ GGRecipeExcOutLabel lab ∨
    GGInndiagUnitaryLabel lab ∨ GGRecipeE6Label lab ∨ GGRecipeTwE6Label lab


@[expose] def GGRawInnFieldDoneLabel (lab : LargeEvenLabel) : Prop :=
  GGLinearRecipeLabel lab ∨ GGSymplecticRecipeLabel lab ∨ GGB2derLabel lab ∨
    GGRecipeSmallExcLabel lab ∨ GGInndiagUnitaryLabel lab ∨ GGRecipeExcInnLabel lab ∨
    GGRecipeE6Label lab ∨ lab.tag = .F4

theorem ggRawInnFieldOn_done : GGRawInnFieldOn GGRawInnFieldDoneLabel :=
  ggRawInnFieldOn_linear.or (ggRawInnFieldOn_symplectic.or (ggRawInnFieldOn_b2der.or
    (ggRawInnFieldOn_smallExc.or (ggRawInnFieldOn_unitary.or (ggRawInnFieldOn_excInn.or
      (ggRawInnFieldOn_E6.or ggRawInnFieldOn_F4))))))

theorem ggRawInnFieldInput_of_rest
    (h : GGRawInnFieldOn fun lab => ¬ GGRawInnFieldDoneLabel lab) : GGRawInnFieldInput :=
  ggRawInnFieldInput_of_on (fun lab _ => em (GGRawInnFieldDoneLabel lab))
    (ggRawInnFieldOn_done.or h)

theorem ggRawFieldCentralOn_done : GGRawFieldCentralOn GGRawFieldCentralDoneLabel :=
  ggRawFieldCentralOn_linear.or (ggRawFieldCentralOn_symplecticHigh.or
    (ggRawFieldCentralOn_b2der.or (ggRawFieldCentralOn_smallExc.or
      (ggRawFieldCentralOn_outCyclic.or (ggRawFieldCentralOn_excOut.or
        (ggRawFieldCentralOn_unitary.or (ggRawFieldCentralOn_E6.or ggRawFieldCentralOn_twE6)))))))

theorem ggRawFieldCentralInput_of_rest
    (h : GGRawFieldCentralOn fun lab => ¬ GGRawFieldCentralDoneLabel lab) :
    GGRawFieldCentralInput :=
  ggRawFieldCentralInput_of_on (fun lab _ => em (GGRawFieldCentralDoneLabel lab))
    (ggRawFieldCentralOn_done.or h)

@[expose] def GGRawPCyclicDoneLabel (lab : LargeEvenLabel) : Prop :=
  GGLinearRecipeLabel lab ∨ GGSymplecticRecipeLabel lab ∨ GGB2derLabel lab ∨
    GGRecipeExcCyclicLabel lab ∨ GGInndiagUnitaryLabel lab ∨ GGRecipeE6Label lab

theorem ggRawPCyclicOn_done : GGRawPCyclicOn fun _ => GGRawPCyclicDoneLabel :=
  ggRawPCyclicOn_linear.or (ggRawPCyclicOn_symplectic.or (ggRawPCyclicOn_b2der.or
    (ggRawPCyclicOn_excCyclic.or (ggRawPCyclicOn_unitary.or ggRawPCyclicOn_E6))))

theorem ggL46CyclicInput_of_rest
    (h : GGRawPCyclicOn fun p lab => GGNotD4Three p lab ∧ ¬ GGRawPCyclicDoneLabel lab)
    (hD4 : GGL46CyclicD4Input) : GGL46CyclicInput := by
  refine ggL46CyclicInput_of_raw (fun p hp hp2 lab hlab hne => ?_) hD4
  by_cases hd : GGRawPCyclicDoneLabel lab
  · exact ggRawPCyclicOn_done p hp hp2 lab hlab hd
  · exact h p hp hp2 lab hlab ⟨hne, hd⟩

end CFSG.StandardType

end
