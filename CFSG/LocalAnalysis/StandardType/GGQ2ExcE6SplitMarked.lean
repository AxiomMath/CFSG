module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitDefs
import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitOccurs
import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitDatum
import CFSG.LocalAnalysis.StandardType.GGQ2ExcE6SplitLabel
import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreOccursDict
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGLinImageSubspace

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.QTwoCav CFSG.StandardType.TableCRes


theorem e6SplitCoreMarked_holds : E6SplitCoreMarked := by
  intro L _ _ p S hS c hadm
  obtain ⟨⟨U, hU⟩, hΛ⟩ := hadm
  have hadm' : ExcRaw.admissible 1 c := ⟨⟨U, hU⟩, hΛ⟩
  obtain ⟨d⟩ := e6SplitCoreDatum_holds S hS
  obtain ⟨A, hA, hAeq⟩ := exists_le_ggLinImage_eq_of_addEquiv (p := 3) d.coord U
  have hc : ExcRaw.occurs 1 (ggLinImage (p := 3) d.coord A) c := by
    rw [hAeq]
    exact hU
  have hcomp := isComponentOf_e6SplitComponent_of_occurs hS d hA hadm' hc
  obtain ⟨a, ha, hT, hap⟩ := exists_family_of_le_fullThreeTorus (hA.trans d.le_fullThreeTorus)
  have hK : CFSG.Open.IsComponentOf (e6SplitComponent S c)
      (S.Γ ⊓ Subgroup.centralizer (Set.range fun u : ↥A => rootDiagUnit .E6 (a u))) := by
    rw [centralizer_range_excFamily ha]
    exact isComponentOf_iff_open.mp hcomp
  obtain ⟨j, hR⟩ := E6SplitDatum.exists_kernelComponent_of_occurs hS d hA ha hc
  have hKj : rationalComponentM S.ρ S.Γ (famCharHom a) j = e6SplitComponent S c :=
    rationalComponentM_eq_e6SplitComponent j hR
  have hKspan : e6SplitComponent S c ≤ rootSpan .E6 L
      {γ | ∃ (k : ℕ) (δ : Fin Tag.E6.rank → ℤ),
        δ ∈ componentRoots (famCharHom a) j ∧
          γ = (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[k] δ} := by
    rw [← hKj]
    simp only [rationalComponentM, rationalSpanM, rationalRootsM]
    exact (Subgroup.commutator_le_self _).trans inf_le_left
  have hchar : CharP L 2 :=
    CFSG.StandardType.LangRat.charP_two_of_langSetup_q_eq_two_pow S (f := 1) (by
      rw [hS.1]
      norm_num)
  obtain ⟨n, hn, hlab⟩ :=
    langFamilyCompLabel_exc (Or.inl rfl) S Nat.prime_three (by norm_num) a hT hap hK j hKspan
  obtain ⟨-, -, hhas, -⟩ := hlab
  have hlabel := componentLabel_e6Split_eq_label (a := a) hS hT j hc hR hn
  rw [hlabel] at hhas
  exact largeEvenMarking_of_hasLabel hcomp.2.2 hΛ hhas

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
