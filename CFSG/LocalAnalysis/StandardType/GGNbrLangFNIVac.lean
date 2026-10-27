module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIVacClassical
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIVacChev
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIVacTwisted
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwisted

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem kgFieldNotInnerInputOn_not_dvd : KGFieldNotInnerInputOn fun p lab => ¬ p ∣ lab.n := by
  intro p lab hp hp2 hlab ht3 hpn
  have hexp : LargeEvenLabelAll lab fun R _ _ F => ∀ f ∈ F, f ^ (kgfniFieldDegree lab * lab.n) = 1 :=
    kgfniFieldExponentOn_of_parts kgfni_fieldExponent_classical
      kgfni_fieldExponent_chev kgfni_fieldExponent_twisted lab hlab trivial
  have hsim : LargeEvenLabelAll lab fun R _ _ _ => IsSimpleGroup R ∧ ∃ a b : R, a * b ≠ b * a :=
    kgfniRawSimpleOn_of_parts kgfni_rawSimple_classical
      kgfni_rawSimple_chev kgfni_rawSimple_twisted lab hlab trivial
  have hconj : LargeEvenLabelAll lab (GGRawFieldConj p) :=
    ggRawFieldConjInputExc_holds p hp hp2 lab hlab ht3
  have hcop := kgfni_coprime_fieldDegree_of_not_t3 hp hp2 ht3 hpn
  refine LargeEvenLabelAll.mono (fun R _ I F h => ?_) (largeEvenLabelAll_and (largeEvenLabelAll_and hsim hexp) hconj)
  obtain ⟨⟨⟨hs, hna⟩, hpow⟩, hc⟩ := h
  haveI := hs
  exact kgFieldNotInnerCont_of_fieldConj_exponent hp hna hc hpow hcop

end CFSG.StandardType
