module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K1Cover
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K1Exc
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K1AltSpor
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811K1Lin
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.TableComplete
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open TauCeti (CFSGIndex)

section

theorem k34odd_of_tables
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hAlt : CFSG.ComponentClassification.SolAltLit.SchurAlternatingMultiplierInput)
    (hSpor : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers) : K34odd := by
  intro L _ _ hq hcat _hodd hrk
  by_cases h3 : 3 ∣ Nat.card (Subgroup.center L)
  · exact Or.inl (k34odd_threeCover_of_three_dvd hGA hAlt hSpor L hq hcat h3 hrk)
  · refine Or.inr ⟨h3, ?_⟩
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hrkX : CFSG.Open.pRank 3 (⊤ : Subgroup (L ⧸ Subgroup.center L)) = 3 :=
      (CFSG.SectionRank.pRank_quotient_eq (Subgroup.center L) h3).trans hrk
    obtain ⟨i, ⟨e⟩⟩ := hcat
    by_cases hlie : ∃ d, i = CFSGIndex.lie d
    · obtain ⟨d, rfl⟩ := hlie
      by_cases hcl : (∃ r q, d.1 = .A r q) ∨ (∃ r q, d.1 = .twistedA r q) ∨
          (∃ r q, d.1 = .B r q) ∨ (∃ r q, d.1 = .C r q) ∨ (∃ r q, d.1 = .D r q) ∨
          (∃ r q, d.1 = .twistedD r q)
      · by_cases hch : d.1.characteristic = 3
        · exact Or.inr (Or.inl (Or.inl
            (k34odd_lie_char3_or_exceptional _ d e hrkX (Or.inl hch))))
        · rcases k34odd_lie_classical_crossChar _ d e hrkX hch hcl with h | h
          · exact Or.inr (Or.inl (Or.inr h))
          · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inl (Or.inl
          (k34odd_lie_char3_or_exceptional _ d e hrkX (Or.inr hcl))))
    · rcases k34odd_nonLie _ i e (fun d h => hlie ⟨d, h⟩)
          (CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian L hq)
          hrkX with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr h))

end

section

theorem k34odd_holds
    : K34odd :=
  k34odd_of_tables CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
    CFSG.Alternating.Multipliers.schurAlternatingMultiplierInput
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.sporadicMultipliers_holds

theorem k1_holds
    : K1 := k34odd_holds

end

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
