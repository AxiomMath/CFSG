module

public import CFSG.LocalAnalysis.StandardType.GGE0ModelFrameOn
public import CFSG.LocalAnalysis.StandardType.GGE0ExcNoSuzukiReeAt
public import CFSG.LocalAnalysis.StandardType.GGSteinbergCorrection
public import CFSG.LocalAnalysis.StandardType.GGE0E6Core
public import CFSG.LocalAnalysis.StandardType.GGOuterInvAtE6

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

theorem ggE0ModelDataAtOn_E6
    : GGE0ModelDataAtOn .E6 (fun f p => ¬ (p = 3 ∧ 3 ∣ 2 ^ f - 1)) := by
  intro n f hadm _
  have hf : 1 ≤ f := hadm.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  refine ⟨CFSG.Blueprint.Chevalley.adjointGroup .E6 (GaloisField 2 f), inferInstance,
    CFSG.LieType.Steinberg.Isogeny.e6Isogeny (GaloisField 2 f),
    (MulAut.conj : CFSG.Blueprint.Chevalley.adjointGroup .E6 (GaloisField 2 f) →*
      MulAut (CFSG.Blueprint.Chevalley.adjointGroup .E6 (GaloisField 2 f))).range ⊔
      (AutSt.e6DiagHom (GaloisField 2 f)).range,
    CFSG.LieType.Steinberg.Isogeny.e6Isogeny_surjective _,
    CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center,
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot, le_sup_left, ?_, ?_⟩
  · intro G _ ψ hker c _ hdiag
    exact ggOuterInv_e6Marking ψ hker hdiag
  · simpa only [hK] using ggE0Model_e6 (GaloisField 2 f)

theorem ggE0AtOn_E6_nonshape
    :
    GGE0AtOn .E6 (fun f p => ¬ (p = 3 ∧ 3 ∣ 2 ^ f - 1)) :=
  ggE0AtOn_of_modelData (ggE0InG1At_of_steinberg ggSteinbergCorrectionAt_E6)
    ggE0ModelDataAtOn_E6

end CFSG.StandardType
