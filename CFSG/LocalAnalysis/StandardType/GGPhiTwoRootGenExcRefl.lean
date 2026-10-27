module

public import CFSG.LocalAnalysis.StandardType.GGPhiTwoRootGenDefs
public import CFSG.LocalAnalysis.StandardType.GGExcSplitRootGenModel
public import CFSG.LocalAnalysis.StandardType.GGExcSplitRootGenRoot

public section

namespace CFSG.StandardType.PhiTwoRootGen

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem phiTwoComp_eq_of_excRefl_eq
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) {K : Type} [Field K]
    {g0 : ModGL τ (AlgebraicClosure K)} {β β' : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hβ' : IsRoot τ β')
    (h : ExcSplitRootGen.excRefl (p := p) β = ExcSplitRootGen.excRefl (p := p) β') :
    phiTwoComp g0 β = phiTwoComp g0 β' := by
  have hiff : ∀ t : Fin τ.rank → ZMod p,
      (∑ j, (β j : ZMod p) * t j = 0) ↔ (∑ j, (β' j : ZMod p) * t j = 0) := by
    intro t
    rw [← ExcSplitRootGen.excRefl_eq_self_iff hp2 hβ,
      ← ExcSplitRootGen.excRefl_eq_self_iff hp2 hβ', h]
  rcases ExcSplitRootGen.eq_or_eq_neg_of_forall_sum_eq_zero hτ hp2 hβ hβ'
      (fun t => (hiff t).1) with h' | h'
  · rw [h']
  · rw [h', phiTwoComp_neg]

end CFSG.StandardType.PhiTwoRootGen

end
