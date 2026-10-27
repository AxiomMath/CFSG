module

public import CFSG.LocalAnalysis.StandardType.GGTBWNormLowRank
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineClassical
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineClassicalLabel
public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIVacClassical

public section

namespace CFSG.StandardType

open CFSG.Assembly


theorem largeEvenLabelAll_wnorm_nineClassical {p : ℕ} {lab : LargeEvenLabel} (hp : p.Prime)
    (hp2 : p ≠ 2) (hlab : LargeEvenInLambda2 lab)
    (hcl : GGTableBNbrInnerNineClassicalLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusWNormSC p R I := by
  unfold GGTableBNbrInnerNineClassicalLabel at hcl
  rcases hcl with ⟨h, hpe⟩ | ⟨h, hpe⟩ | ⟨ht, hpe⟩ | ⟨ht, hl, hpe⟩
  · exact (largeEvenLabelAll_card_lt_linear_of_ord hp hp2 h hpe).mono
      fun _ _ _ _ hX => ggTorusWNormSC_of_card_lt hX
  · have htag : KGFNIClassicalLabel lab := by
      unfold KGFNIClassicalLabel
      rcases h with ⟨ht, -⟩ | ⟨ht, -⟩ <;> simp [ht]
    exact ((kgfni_rawSimple_classical lab hlab htag).and
      (largeEvenLabelAll_card_lt_unitary_of_ord hp hp2 hlab h hpe)).mono
      fun _ _ _ _ h => ggTorusWNormSC_of_card_lt (h.2 h.1.1 h.1.2)
  · exact (largeEvenLabelAll_card_lt_symplectic_of_ord hp hp2 hlab ht hpe).mono
      fun _ _ _ _ hX => ggTorusWNormSC_of_card_lt hX
  · have htag : KGFNIClassicalLabel lab := by
      unfold KGFNIClassicalLabel
      rcases ht with ht | ht <;> simp [ht]
    exact ((kgfni_rawSimple_classical lab hlab htag).and
      (largeEvenLabelAll_card_lt_orthogonal_of_ord hp hp2 ht hl hpe)).mono
      fun _ _ _ _ h => ggTorusWNormSC_of_card_lt (h.2 h.1.1 h.1.2)

end CFSG.StandardType
