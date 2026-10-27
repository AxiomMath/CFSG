module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2InvolutionInnerOfOddRange
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2Action
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Involution images in the Section-4 semilinear action
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

public theorem secondCase_psl2_action_involution_inner
    {G : Type u} [Group G] [Finite G]
    {c : CentralizerSetup G} (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (K : Type u) [Field K] [Finite K]
    (ad : SecondCasePSL2ActionData w d K)
    (r : w.M) (hrI : IsInvolution (r : G)) :
    ∃ z : PGL2 K, ad.f r = SemidirectProduct.inl z := by
  have hr2G : (r : G) ^ 2 = 1 := hrI.2
  have hr2 : r ^ 2 = 1 := Subtype.ext hr2G
  have hodd : Odd (Nat.card (pGammaL2FieldProjection K ad.f.range).range) :=
    ad.fieldRange_odd
  exact pGammaL2_involution_mem_inner_of_odd_field_range
    ad.f.range hodd (by exact ⟨r, rfl⟩) (by simpa using congrArg ad.f hr2)

end CFSG.GorensteinWalter
