module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseHhatInvolutionCount
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.FirstCaseOrderInfra
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section
namespace CFSG.GorensteinWalter
universe u

/-- The base part of the Klein-four count, with one Hall witness shared by
the `H` and `Ĥ` involution formulas. -/
public theorem firstCase_klein_base_count_package
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (hfirst : FirstCase c)
    (hklein : IsKleinFour (pCore 2 c.Hhat)) :
    ∃ K : Subgroup G,
      IsHallIn K c.FU ∧ K ≠ ⊥ ∧
      Nat.card {x : G // IsInvolution x ∧ x ∈ c.H} =
        3 + 2 * Nat.card K ∧
      Nat.card {x : G // IsInvolution x ∧ x ∈ c.Hhat} =
        3 + 6 * Nat.card K ∧
      c.H.index = 3 * c.Hhat.index := by
  obtain ⟨K, hK, hKne, hHcount, hHhatcount⟩ :=
    firstCase_klein_Hhat_involution_count_with_K hmin c hfirst hklein
  exact ⟨K, hK, hKne, hHcount, hHhatcount,
    firstCase_H_index_eq_three_mul_Hhat_index hmin c hfirst hklein⟩

end CFSG.GorensteinWalter
