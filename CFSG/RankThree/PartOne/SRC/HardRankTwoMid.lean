module

public import CFSG.RankThree.PartOne.SRC.Split
public import CFSG.RankThree.PartOne.SRC.ModelU4Two
public import CFSG.RankThree.PartOne.SRC.ModelSp4Two
import CFSG.Adapters.LinearCatalog
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier

public section

namespace CFSG.RankThree.PartOne.SRC

open TauCeti CFSG.RankThree.PartOne.N143


theorem noHardRankTwoMid : NoLowTwoRankSectionFor IsHardRankTwoMidIndex := by
  refine noLowTwoRankSectionFor_of_rankFourCover fun i hi => ?_
  rcases i with ⟨p, hp⟩ | ⟨n, hn⟩ | ⟨⟨li, hv⟩⟩ | ⟨s⟩
  · exact (hi : False).elim
  · exact (hi : False).elim
  · cases li <;> first | exact (hi : False).elim | skip
    · obtain ⟨hr, hq2, he, h9⟩ := hi
      subst hr
      rename_i q
      have h9q : q.p ^ q.exponent ≠ 9 := by rw [← PrimePower.card_def]; exact h9
      have : Fact q.p.Prime := ⟨q.prime_p⟩
      have hcard : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
        GaloisField.card _ _ q.exponent_pos.ne'
      exact ⟨q.p, q.prime_p, hq2, rankFourCover_of_mulEquiv
        (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 3 q hv)
        (rankFourCover_psl4_two (F := GaloisField q.p q.exponent) hcard hq2 he
          (by rw [hcard]; exact h9q))⟩
    · obtain ⟨hr, hq2, he, h9⟩ := hi
      subst hr
      rename_i q
      have h9q : q.p ^ q.exponent ≠ 9 := by rw [← PrimePower.card_def]; exact h9
      have hℓ : ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩ = q.p := by
        simp [ValidLieTypeIndex.characteristic]
      have hfe : ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 q, hv⟩ = q.exponent := by
        simp [ValidLieTypeIndex.fieldExponent]
      have hpr : (ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩).Prime := by
        rw [hℓ]; exact q.prime_p
      have : Fact (ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩).Prime := ⟨hpr⟩
      have hp2 : ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩ ≠ 2 := by rw [hℓ]; exact hq2
      have he2 : 2 ≤ ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 q, hv⟩ := by rw [hfe]; exact he
      have h9' : ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩ ^
          ValidLieTypeIndex.fieldExponent ⟨.twistedA 3 q, hv⟩ ≠ 9 := by
        rw [hℓ, hfe]; exact h9q
      exact ⟨ValidLieTypeIndex.characteristic ⟨.twistedA 3 q, hv⟩, hpr, hp2,
        rankFourCover_of_mulEquiv
          (CFSG.QuasithinUnique.SQTK.typeTwistedAGroupEquivStatedProj 3 q hv)
          (rankFourCover_psu4_two hp2 he2 h9')⟩
    · obtain ⟨hr, hq2, he, h9⟩ := hi
      subst hr
      rename_i q
      have h9q : q.p ^ q.exponent ≠ 9 := by rw [← PrimePower.card_def]; exact h9
      have hc : ValidLieTypeIndex.characteristic ⟨.B 2 q, hv⟩ = q.p :=
        LieTypeIndex.characteristic_B 2 q
      have hfe : ValidLieTypeIndex.fieldExponent ⟨.B 2 q, hv⟩ = q.exponent :=
        LieTypeIndex.fieldExponent_B 2 q
      have hpr : (ValidLieTypeIndex.characteristic ⟨.B 2 q, hv⟩).Prime := by
        rw [hc]; exact q.prime_p
      have : Fact (ValidLieTypeIndex.characteristic ⟨.B 2 q, hv⟩).Prime := ⟨hpr⟩
      have hp2 : ValidLieTypeIndex.characteristic ⟨.B 2 q, hv⟩ ≠ 2 := by rw [hc]; exact hq2
      have he2 : 2 ≤ ValidLieTypeIndex.fieldExponent ⟨.B 2 q, hv⟩ := by rw [hfe]; exact he
      have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨.B 2 q, hv⟩
      have hKc : Nat.card ↥(ValidLieTypeIndex.fixedField ⟨.B 2 q, hv⟩) =
          ValidLieTypeIndex.characteristic ⟨.B 2 q, hv⟩ ^
            ValidLieTypeIndex.fieldExponent ⟨.B 2 q, hv⟩ := by
        rw [ValidLieTypeIndex.card_fixedField, ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]
      exact ⟨ValidLieTypeIndex.characteristic ⟨.B 2 q, hv⟩, hpr, hp2,
        rankFourCover_of_mulEquiv
          (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv)
          (rankFourCover_psp4_two (K := ↥(ValidLieTypeIndex.fixedField ⟨.B 2 q, hv⟩))
            (p := ValidLieTypeIndex.characteristic ⟨.B 2 q, hv⟩)
            (e := ValidLieTypeIndex.fieldExponent ⟨.B 2 q, hv⟩) hKc hp2 he2
            (by rw [hKc, hc, hfe]; exact h9q))⟩
  · exact (hi : False).elim

end CFSG.RankThree.PartOne.SRC
