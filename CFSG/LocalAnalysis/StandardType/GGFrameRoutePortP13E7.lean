module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP13Cent
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBTorus
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP13E7Cent
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP13E7Move
import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBSelfCent

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.OddStandard.SmallF3.Omega.E7RootSet
  Certificates.OmegaSevenMax TableBExcTwo TableBExcTwoTB

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

theorem p13a6_E7
    {k : Type} [Field k] [Finite k]
    [CharP k 2] (hk : Nat.card k = 2) {K : Type} [Group K] [Finite K] {E : Subgroup K}
    (e : K ≃* adjointGroup .E7 k)
    (hE : E.map e.toMonoidHom = (TableBExcTwoTB.tE k TableBExcTwo.frameE7).range) :
    P13aConclusion K E 7 := by
  refine p13aConclusion_of_mulEquiv e ?_
  rw [hE]
  refine p13aConclusion_of_cases ?_ (centralizer_tE_frameE7 hk) fun F hF hidx => ?_
  · calc
      Nat.card (tE k frameE7).range = Nat.card (Multiplicative (Fin 7 → ZMod 3)) :=
        Nat.card_congr (Equiv.ofInjective (tE k frameE7) (tE_injective frameE7)).symm
      _ = Nat.card (Fin 7 → ZMod 3) := Nat.card_congr Multiplicative.toAdd
      _ = 3 ^ 7 := by rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  obtain ⟨ψ, hψ, rfl⟩ := p13e7_exists_hyp hF hidx
  by_cases hr : ∃ β, IsRoot Tag.E7 β ∧ (redV β = ψ ∨ redV β = -ψ)
  · obtain ⟨β, hβ, hβψ⟩ := hr
    have hψβ : p13e7Hyp k ψ = p13e7Hyp k (redV β) := by
      rcases hβψ with h | h
      · rw [h]
      · rw [h]
        exact (p13e7Hyp_neg ψ).symm
    obtain ⟨c, hcT, hcF⟩ := p13e7_exists_conj_hyp hk hβ
    refine p13aCase_of_mulEquiv (MulAut.conj c) ?_
    rw [hcT, hψβ, hcF]
    exact p13e7_case_frame hk
  · push Not at hr
    exact Or.inl (p13e7_centralizer_hyp_of_not_root hk hψ hr)

end CFSG.StandardType.FrameRoute
