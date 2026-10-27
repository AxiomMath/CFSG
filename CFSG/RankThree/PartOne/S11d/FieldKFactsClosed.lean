module

public import CFSG.RankThree.PartOne.S11d.FieldKFactsFinal
public import CFSG.RankThree.PartOne.KEXC.Involution
public import CFSG.RankThree.PartOne.KEXC.OddCenterLie
public import CFSG.SignalizerFunctorTheorem.NonLocalExc.Chevalley
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeReeTits

public section

namespace CFSG.RankThree.PartOne.FieldFix


theorem chevalleySubfieldNonLocalized : ChevalleySubfieldNonLocalized :=
  fun τ hτ σ => CFSG.SignalizerFunctorTheorem.NonLocalExc.nonLocalized_chevalley τ hτ σ

theorem largeReeTitsNonLocalized : LargeReeTitsNonLocalized :=
  CFSG.SignalizerFunctorTheorem.CatalogBridge.subfieldNonLocalizedLargeReeTits

theorem fieldAutCoset_closed : FieldAutCoset :=
  fieldAutCoset_final chevalleySubfieldNonLocalized largeReeTitsNonLocalized

theorem fieldFixedPElements_closed : FieldFixedPElements :=
  fieldFixedPElements_final chevalleySubfieldNonLocalized largeReeTitsNonLocalized

theorem fieldFixedCentralizer_closed : FieldFixedCentralizer :=
  fieldFixedCentralizer_final chevalleySubfieldNonLocalized largeReeTitsNonLocalized

theorem fieldFixedNonLocal_closed : FieldFixedNonLocal :=
  fieldFixedNonLocal_final chevalleySubfieldNonLocalized largeReeTitsNonLocalized

theorem fieldFixedTwoElements_closed : FieldFixedTwoElements :=
  fieldFixedTwoElements_of_tags
      (tagFixedFacts_all chevalleySubfieldNonLocalized largeReeTitsNonLocalized)
      KEXC.largeReeNoInvolution_holds KEXC.oddCenterLie_holds

end CFSG.RankThree.PartOne.FieldFix
