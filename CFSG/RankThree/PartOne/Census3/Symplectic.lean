module

public import CFSG.RankThree.PartOne.Census3.Interface
import CFSG.RankThree.PartTwo.Census.OddClassical.SymplecticWitness
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2Carrier

public section

namespace CFSG.RankThree.PartOne.Census3

open CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.Assembly.LowTwoRank
  CFSG.RankThree.PartTwo.Census TauCeti

theorem theoremThreeCase_B2 (q : PrimePower) (hv : (LieTypeIndex.B 2 q).Valid) :
    TheoremThreeCase (.lie ⟨.B 2 q, hv⟩) := by
  by_cases hq : q.p = 2
  · exact fun G _ _ _ e => TheoremThreeList.of_B2_even hv hq e
  by_cases hf : q.exponent = 1
  · exact fun G _ _ _ e => TheoremThreeList.of_B2_prime hv hq hf e
  have hc : ValidLieTypeIndex.characteristic ⟨.B 2 q, hv⟩ = q.p :=
    LieTypeIndex.characteristic_B 2 q
  have he : ValidLieTypeIndex.fieldExponent ⟨.B 2 q, hv⟩ = q.exponent :=
    LieTypeIndex.fieldExponent_B 2 q
  have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨.B 2 q, hv⟩
  have h2 := le_localRank_PSp_two (p := ValidLieTypeIndex.characteristic ⟨.B 2 q, hv⟩)
    (f := ValidLieTypeIndex.fieldExponent ⟨.B 2 q, hv⟩)
    (K := ↥(ValidLieTypeIndex.fixedField ⟨.B 2 q, hv⟩)) (by rw [hc]; exact hq) (by
      rw [ValidLieTypeIndex.card_fixedField, ValidLieTypeIndex.fieldOrder_eq_characteristic_pow])
  rw [he] at h2
  have h4 : 4 ≤ localRank (ValidLieTypeIndex.characteristic ⟨.B 2 q, hv⟩)
      (StatedProj (StatedSp 2 ↥(ValidLieTypeIndex.fixedField ⟨.B 2 q, hv⟩))) := by
    have := q.exponent_pos
    omega
  exact (excludedIndex_of_equiv
    (fun _ => ⟨CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv⟩) Fact.out
    (by rw [hc]; exact hq) h4).case

theorem theoremThreeCase_C (r : ℕ) (q : PrimePower) (hv : (LieTypeIndex.C r q).Valid) :
    TheoremThreeCase (.lie ⟨.C r q, hv⟩) := by
  have hrange := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  have hc : ValidLieTypeIndex.characteristic ⟨.C r q, hv⟩ = q.p :=
    LieTypeIndex.characteristic_C r q
  have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField ⟨.C r q, hv⟩
  have h4 := four_le_localRank_PSp (p := ValidLieTypeIndex.characteristic ⟨.C r q, hv⟩)
    (f := q.exponent) (K := ↥(ValidLieTypeIndex.fixedField ⟨.C r q, hv⟩))
    (by rw [hc]; exact hrange.2) (by
      rw [ValidLieTypeIndex.card_fixedField, hc]
      simp [ValidLieTypeIndex.fieldOrder]) q.exponent_pos hrange.1
  exact (excludedIndex_of_equiv
    (fun _ => ⟨CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj r q hv⟩) Fact.out
    (by rw [hc]; exact hrange.2) h4).case

end CFSG.RankThree.PartOne.Census3
