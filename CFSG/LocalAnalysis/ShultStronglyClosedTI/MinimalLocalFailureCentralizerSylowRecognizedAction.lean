module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePoint
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTripleSylowMaximalityActions
public import CFSG.CharacterTheory.TwoRankLowerBound.Helpers

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.CentralizerSylow

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePoint
open CFSG.ShultStronglyClosedTI.TripleSylowMaximality

universe u v

variable {G : Type u} [Group G] [Finite G]

theorem two_le_twoRank_of_native (hrank : TwoRankAtLeastTwo G) : 2 ≤ twoRank G := by
  obtain ⟨E, hcard, hsquare⟩ := hrank
  have hE : IsElemAbelian 2 E := by
    refine ⟨CFSG.BenderSuzuki.isMulCommutative_of_forall_sq_one hsquare, ?_⟩
    intro e he
    exact congrArg Subtype.val (hsquare ⟨e, he⟩)
  exact CFSG.TwoRankLowerBound.Helpers.le_twoRank_of_elementary G E hE 2
    (by simpa only [Nat.reducePow] using hcard)

theorem recognized_action_three_point_normalizer
    {Ω : Type v} [MulAction G Ω] [Finite Ω]
    (hrank : TwoRankAtLeastTwo G) (hR1 : R1Full G)
    (htrans : MulAction.IsPretransitive G Ω) (alpha : Ω)
    (hA : fusionStronglyEmbedded (MulAction.stabilizer G alpha))
    (z : G) (hzalpha : z • alpha = alpha) (hz : orderOf z = 2)
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (P : Subgroup G) (hP : IsPGroup p P) (hPalpha : P ≤ MulAction.stabilizer G alpha)
    (hthree : 3 ≤ Nat.card {omega : Ω // omega ∈ fixedPointsOfSubgroup G Ω P})
    (hintersection : ∃ T : Sylow p (CFSG.oddCore G),
      (T : Subgroup (CFSG.oddCore G)).map (CFSG.oddCore G).subtype = P ⊓ CFSG.oddCore G) :
    (conjugacyWithin (MulAction.stabilizer G alpha) z ∩
      (Subgroup.normalizer (P : Set G) : Set G)).Nonempty := by
  let A := MulAction.stabilizer G alpha
  have hcoset : 3 ≤ Nat.card (pointFixedSet A P) := by
    rw [rightCoset_fixed_card]
    have hcard := Nat.card_congr (actionCosetFixedEquiv htrans alpha P)
    change Nat.card {omega : G ⧸ A // ∀ p ∈ P, p • omega = omega} =
      Nat.card {omega : Ω // omega ∈ fixedPointsOfSubgroup G Ω P} at hcard
    rw [hcard]
    exact hthree
  exact recognized_three_point_p_subgroup_involution_normalizer
    (two_le_twoRank_of_native hrank) hR1 A hA z
    (MulAction.mem_stabilizer_iff.mpr hzalpha) hz p hp hpodd P hP hPalpha hcoset hintersection

end CFSG.ShultStronglyClosedTI.CentralizerSylow
