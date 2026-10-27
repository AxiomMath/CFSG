module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.OfType
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.Split
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverFamilies
import CFSG.Adapters.LieModelSimple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm

open CFSG.Open CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.AGLEmbedding.ParabHub
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

theorem permWitnessPSp_holds : PermWitnessPSp := by
  intro G _ _ m hm hL
  have : IsSimpleGroup G := LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL
  have hS : StatedClassicalModel G .PSp m 2 1 := hL.statedClassicalModel (by decide)
  obtain ⟨-, F, hF, hFfin, hcard, ⟨e⟩⟩ := hS
  have := Fintype.ofFinite F
  have hF2 : Nat.card F = 2 := by simpa using hcard
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have h := borelQuotient_sp e
  have hM : Nat.card F - 1 ∣ 3 := by rw [hF2]; norm_num
  have h6 : ∀ j : Fin (rootDatum m F).rank,
      Nat.card (rankOne (rootDatum m F).rootGroup j) = 6 ∧
        ∃ a ∈ rankOne (rootDatum m F).rootGroup j,
          ∃ b ∈ rankOne (rootDatum m F).rootGroup j, a * b ≠ b * a := by
    intro j
    obtain ⟨φ, hφ, hx, hy⟩ := Sp.rankOne (F := F) j
    exact rankOne_six_of_sl2 hF2 Sp.isParametrization hφ hx hy
  have hrank : (rootDatum m F).rank = m := rfl
  have hconn := diagram_connected_of_card_six h (h6 ⟨0, by rw [hrank]; omega⟩)
  have h3 : ∀ j, HasOrderThree (rootDatum m F) j :=
    fun j => (hasSL2Node_sp j).hasOrderThree
  have h3nc : ∀ j, CFSG.AGLEmbedding.BlockCyc.HasOrderThreeNC (rootDatum m F) j :=
    fun j => (hasSL2Node_sp j).hasOrderThreeNC
  exact permWitness_of_borelQuotient_split h hM hconn hm h6 h3 h3nc

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm
