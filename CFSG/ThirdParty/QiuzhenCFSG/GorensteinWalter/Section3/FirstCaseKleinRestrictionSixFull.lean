module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinRestrictionSixIndex
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinIntersectionOddCoreIndex
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseKleinCosetInvolution
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG
noncomputable section
open scoped Pointwise
namespace CFSG.GorensteinWalter
universe u

public theorem firstCase_klein_restrictionSix
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat))
    {y : G} (hy : IsInvolution y) (hyH : y ∉ c.Hhat)
    (hI : 4 ≤ firstCaseCosetInvolutions c y) :
    ∃ s : G, IsInvolution s ∧
      s ∈ (c.Hhat ⊓ conjugateSubgroup c.Hhat y) ∧ s * y = y * s ∧
      (Nat.card {x : G // x ∈ invertedElements
          (oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat y : Subgroup G)) y} ≠ 1 ∨
       Nat.card {x : G // x ∈ invertedElements
          (oddCoreOf (c.Hhat ⊓ conjugateSubgroup c.Hhat y : Subgroup G)) (s * y)} ≠ 1) := by
  have hI' : 4 ≤ Nat.card {x : G // x ∈ invertedElements c.Hhat y} := by
    rw [← firstCase_klein_coset_involution_card_eq c hy hyH]
    exact hI
  have hidx := firstCase_klein_restrictionSix_index_eq hmin c hfirst hklein hy hyH hI'
  have hOidx := firstCase_klein_intersection_oddCore_index_two_of_index_six
    hmin c hfirst hklein hy hyH hidx
  exact firstCase_klein_restrictionSix_oddCore_of_index_two c hy hyH hOidx hI'

end CFSG.GorensteinWalter

