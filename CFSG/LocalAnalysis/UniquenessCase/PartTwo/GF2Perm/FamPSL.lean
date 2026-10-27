module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.OfType
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.Split
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverFamilies
import CFSG.Adapters.LieModelSimple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm

open CFSG.Open CFSG.LieType.Universal CFSG.LieType.Universal.SpecialLinear
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

theorem permWitnessPSL_holds : PermWitnessPSL := by
  intro G _ _ m hm hL
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hk3 : 3 ≤ k := by omega
  have hS : StatedClassicalModel G .PSL (k + 1) 2 1 := hL.statedClassicalModel (by decide)
  have : IsSimpleGroup G :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL
  obtain ⟨⟨-, -, -, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := hS
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hF2 : Nat.card F = 2 := by simpa using hcard
  have hM : Nat.card F - 1 ∣ 3 := by rw [hF2]; norm_num
  let ee : Matrix.ProjectiveSpecialLinearGroup (Fin (k + 1)) F ≃* G :=
    (projectiveSpecialLinearGroupEquivStatedProj (k + 1) F).trans e.symm
  have h : BorelQuotient (rootDatum k F) (weylRep k F) (torus k F)
      (ee.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center _))) (Nat.card F - 1) :=
    borelQuotient_sl ee
  have h6 : ∀ j : Fin k, Nat.card (rankOne (rootDatum k F).rootGroup j) = 6 ∧
      ∃ a ∈ rankOne (rootDatum k F).rootGroup j,
        ∃ b ∈ rankOne (rootDatum k F).rootGroup j, a * b ≠ b * a := by
    intro j
    obtain ⟨φ, hφ, hx, hy⟩ := SL.rankOne (F := F) j
    exact rankOne_six_of_sl2 hF2 SL.isParametrization hφ hx hy
  refine permWitness_of_borelQuotient_split h hM ?_ ?_ h6 (fun j => ?_) (fun j => ?_)
  · exact diagram_connected_of_card_six h (h6 ⟨0, by omega⟩)
  · exact hk3
  · exact (hasSL2Node_sl (F := F) j).hasOrderThree
  · exact (hasSL2Node_sl (F := F) j).hasOrderThreeNC

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm
