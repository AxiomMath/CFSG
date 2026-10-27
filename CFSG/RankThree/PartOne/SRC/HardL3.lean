module

public import CFSG.RankThree.PartOne.SRC.ModelL3
public import CFSG.RankThree.PartOne.SRC.ModelU3
import CFSG.Adapters.LinearCatalog
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.RankThree.PartOne.SRC

open TauCeti CFSG.RankThree.PartOne.N143


theorem noHardL3 : NoLowTwoRankSectionFor IsHardL3Index := by
  refine noLowTwoRankSectionFor_of_rankFourCover fun i hi => ?_
  rcases i with ⟨p, hp⟩ | ⟨n, hn⟩ | ⟨⟨li, hv⟩⟩ | ⟨s⟩
  · exact (hi : False).elim
  · exact (hi : False).elim
  · cases li <;> first | exact (hi : False).elim | skip
    · obtain ⟨hr, hq2, he⟩ := hi
      subst hr
      rename_i q
      have : Fact q.p.Prime := ⟨q.prime_p⟩
      exact ⟨q.p, q.prime_p, hq2, rankFourCover_of_mulEquiv
        (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv)
        (rankFourCover_psl3 (F := GaloisField q.p q.exponent)
          (GaloisField.card _ _ q.exponent_pos.ne') hq2 he)⟩
    · obtain ⟨hr, hq2, he⟩ := hi
      subst hr
      rename_i q
      have hℓ : ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = q.p := by
        simp [ValidLieTypeIndex.characteristic]
      have hfe : ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = q.exponent := by
        simp [ValidLieTypeIndex.fieldExponent]
      have hpr : (ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩).Prime := by
        rw [hℓ]; exact q.prime_p
      have : Fact (ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩).Prime := ⟨hpr⟩
      have hp2 : ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ ≠ 2 := by rw [hℓ]; exact hq2
      have he4 : 4 ≤ ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ := by rw [hfe]; exact he
      exact ⟨ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩, hpr, hp2,
        rankFourCover_of_mulEquiv
          (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 2 q hv)
          (rankFourCover_psu3 hp2 he4)⟩
  · exact (hi : False).elim

end CFSG.RankThree.PartOne.SRC
