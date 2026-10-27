module

public import CFSG.RankThree.PartOne.SLBN.Psp4Nine
public import CFSG.RankThree.PartOne.SRC.Split
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier

public section

namespace CFSG.RankThree.PartOne.SLBN

open TauCeti CFSG.RankThree.PartOne.SRC

theorem rankFourCover_hardPSp4Nine :
    ∀ i : CFSGIndex, IsHardPSp4NineIndex i → RankFourCover 3 i.Group := by
  intro i hi
  rcases i with ⟨p, hp⟩ | ⟨n, hn⟩ | ⟨⟨li, hv⟩⟩ | ⟨s⟩
  · exact (hi : False).elim
  · exact (hi : False).elim
  · cases li <;> first | exact (hi : False).elim | skip
    obtain ⟨hr, hq⟩ := hi
    subst hr
    rename_i q
    have hc : ValidLieTypeIndex.characteristic ⟨.B 2 q, hv⟩ = q.p :=
      LieTypeIndex.characteristic_B 2 q
    have hfe : ValidLieTypeIndex.fieldExponent ⟨.B 2 q, hv⟩ = q.exponent :=
      LieTypeIndex.fieldExponent_B 2 q
    have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨.B 2 q, hv⟩
    have hKc : Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.B 2 q, hv⟩) = 9 := by
      rw [ValidLieTypeIndex.card_fixedField, ValidLieTypeIndex.fieldOrder_eq_characteristic_pow,
        hc, hfe, ← PrimePower.card_def]
      exact hq
    exact rankFourCover_of_mulEquiv
      (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv) (rankFourCover_psp4_nine hKc)
  · exact (hi : False).elim

end CFSG.RankThree.PartOne.SLBN
