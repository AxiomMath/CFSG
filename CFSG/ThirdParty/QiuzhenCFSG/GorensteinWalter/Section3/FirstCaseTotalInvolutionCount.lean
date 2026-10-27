module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.InvolutionCountInSubgroup
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-! The global involution class is the `H`-coset orbit of the distinguished
involution `t`, so its cardinality is the index of `H`. -/

public theorem firstCase_total_involution_card_eq_H_index
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) :
    Nat.card {x : G // IsInvolution x} = c.H.index := by
  have hcard := involutions_card_eq_centralizer_index_of_fusion c.t
    c.t_involution (by
      intro x hx
      obtain ⟨g, hg⟩ := fact_2_preamble_involutions_conjugate hmin x c.t hx
        c.t_involution
      exact ⟨g, hg⟩)
  simpa [c.H_eq_centralizer] using hcard

end CFSG.GorensteinWalter
