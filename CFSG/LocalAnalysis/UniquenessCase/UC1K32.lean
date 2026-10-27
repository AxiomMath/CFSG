module

public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankOneFinal

import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.Bridge
import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27StructTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup

set_option linter.unusedSectionVars false


theorem k32_holds
    : K32 := by
  intro L _ _ hK hs hnab h1
  obtain ⟨i, hi⟩ := hK.isCatalogGroup_of_surjective ⊤ hnab (Subgroup.subtype ⊤)
    (fun x => ⟨⟨x, trivial⟩, rfl⟩)
  rcases CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.ThreeRankCls.kFactThreeRankOneSimple
      L hs hnab i hi h1 with
    ⟨⟨d, hv⟩, hd, he⟩ | hJ | hA5
  · rcases he with ⟨e⟩
    rcases hd with ⟨q, _hp, hA⟩ | ⟨q, hc, hA⟩ | ⟨q, hc, hA⟩
    · subst hA
      exact Or.inl ⟨q.p, q.exponent,
        CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_A 1 q hv e⟩
    · subst hA
      have hq : q.p ^ q.exponent % 3 = 2 := by
        rw [← TauCeti.PrimePower.card_def q]; exact hc
      exact Or.inr (Or.inl ⟨q.p, q.exponent, hq,
        CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_A 2 q hv e⟩)
    · subst hA
      have hq : q.p ^ q.exponent % 3 = 1 := by
        rw [← TauCeti.PrimePower.card_def q]; exact hc
      exact Or.inr (Or.inr (Or.inl ⟨q.p, q.exponent, hq,
        CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_twistedA 2 q hv e⟩))
  · rcases hJ with ⟨eJ⟩
    obtain ⟨g⟩ := CFSG.Sporadic.Bridge.J1.nonempty_mulEquiv
    exact Or.inr (Or.inr (Or.inr ⟨eJ.trans g.symm⟩))
  · rcases hA5 with ⟨eA⟩
    exact Or.inl ⟨2, 2, CFSG.OddStandard.Seitz77.lieModel_of_alt eA⟩

end CFSG.LocalAnalysis.UniquenessCase.UCK
