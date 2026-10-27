module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2ExcCommon
import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

theorem w135c2_four_le_mQuot_sz
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L : Subgroup (MulAut W)} {t : MulAut W} (hctx : Is135Context Y L) (htY : t ∈ Y)
    (ht2 : orderOf t = 2) {n f : ℕ}
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .twistedB2 n 2 f) :
    4 ≤ E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← pow_two]; exact hW w
  have : Finite (MulAut W) := MulEquiv.finite_left
  have hq : IsQuasisimple ↥L := hctx.2.2.2.2.1
  have hirr : IsIrrOn L ⊤ ⊥ := hctx.2.2.2.2.2
  have : Nontrivial W := by
    obtain ⟨v, -, hv⟩ := SetLike.exists_of_lt hirr.1
    exact ⟨⟨v, 1, fun h => hv (h ▸ Subgroup.one_mem _)⟩⟩
  obtain ⟨-, a, ha, K, _, _, hfa, hK, ⟨α⟩⟩ := (CFSG.Blueprint.LieModel.suzukiModel hlie).2
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  obtain ⟨-, -, hP2, hdisp, -⟩ :=
    CFSG.QuasithinUnique.Setup.Family.suzuki_irreducible_normalizer_excludes a ha hK' W hW' L
      hq.1 (fun U hU => hirr.2.2.2 U hU bot_le le_top) α
  have hN := w135c2_mem_normalizer_of_ctx hctx htY ht2
  have hP : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2, pow_one])
  have htL : t ∈ L := hP2 _ hP (Subgroup.zpowers_le.2 hN) (Subgroup.mem_zpowers t)
  obtain ⟨x, hxt⟩ : ∃ x : ↥L, (x : MulAut W) = t := ⟨⟨t, htL⟩, rfl⟩
  have hx2 : orderOf x = 2 := by rw [← ht2, ← hxt]; exact (Subgroup.orderOf_coe x).symm
  have h1 := hdisp x hx2
  rw [hxt, w135c2_card_range_eq_index t] at h1
  have h2 := w135c2_le_mQuot_of_two_pow_le_index hW t h1
  omega

end CFSG.LocalAnalysis.WeakClosure81
