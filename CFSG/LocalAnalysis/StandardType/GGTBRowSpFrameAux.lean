module

public import CFSG.LocalAnalysis.StandardType.GGTBRowSignedFrameW
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpModel
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiag
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitClassical

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableBSymp SpModel

theorem ggSpRow_recipe_signedFrame {l n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ 2 ^ n - 1) (hl : 1 ≤ l) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSymplectic l (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic l (2 ^ n) false fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusSignedFrameW p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  have hpq : p ∣ Nat.card K - 1 := by
    rw [hK]
    exact hpn
  have : NeZero l := ⟨by omega⟩
  exact ⟨K, inferInstance, inferInstance, hK, hQ, l,
    ggTorusLift_symplectic hp hp2 hpq hl,
    ggTorusSignedFrameW_of_signedElt hp hp2 sp_I_subset_inn center_spProj_eq_bot
      (SpModel.ggTorusSignedElt_sp hp hp2 hpq)⟩

theorem ggSpRow_labelAll_frame {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGReflSpLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGTorusSignedFrameW p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn⟩ := h
  intro Q hQ
  rcases htag with h | h <;> dsimp only at h <;> subst h <;>
    exact ggSpRow_recipe_signedFrame hp hp2 hpn
      (le_trans (by norm_num) hlab.2.1) hQ

theorem ggSpRow_labelAllGuard_frame {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h : GGReflSpLabel p lab) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGTorusSignedFrameW p r R I) :=
  nbrC_labelAll_guard (ggSpRow_labelAll_frame hp hp2 hlab h)

end CFSG.StandardType

end
