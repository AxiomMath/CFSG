module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.OfType
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.Split
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverFamilies
import CFSG.Adapters.LieModelSimple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm

open CFSG.Open CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.AGLEmbedding.ParabHub
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

theorem permWitnessOmegaPlus_holds : PermWitnessOmegaPlus := by
  intro G _ _ m hm hL
  have hS : StatedClassicalModel G .POmegaPlus m 2 1 := hL.statedClassicalModel (by decide)
  have : IsSimpleGroup G :=
    LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL
  obtain ⟨⟨-, -, hn⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := hS
  have := Fintype.ofFinite F
  have hF2 : Nat.card F = 2 := by simpa using hcard
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hn3 : 3 ≤ m := by omega
  have : NeZero m := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus m F)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := m) (K := F))
  have hBQ := borelQuotient_spinPlus hn3 e
  have h6 : ∀ j, Nat.card (rankOne (plusDatum m F hn3).rootGroup j) = 6 ∧
      ∃ a ∈ rankOne (plusDatum m F hn3).rootGroup j,
        ∃ b ∈ rankOne (plusDatum m F hn3).rootGroup j, a * b ≠ b * a := by
    intro j
    obtain ⟨φ, hφ, hx, hy⟩ := SpinPlus.rankOne (K := F) hn3 j
    exact rankOne_six_of_sl2 hF2 (SpinPlus.isParametrization (K := F) hn3) hφ hx hy
  exact permWitness_of_borelQuotient_split hBQ (by rw [hcard]; norm_num)
    (diagram_connected_of_card_six hBQ (h6 (⟨0, by omega⟩ : Fin m)))
    (by change 3 ≤ m; omega) h6
    (fun j => (hasSL2Node_spinPlus hn3 j).hasOrderThree)
    (fun j => (hasSL2Node_spinPlus hn3 j).hasOrderThreeNC)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm
