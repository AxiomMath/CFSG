module

public import CFSG.LocalAnalysis.StandardType.GGQTwoFinishGen

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

theorem ggQ2_finishK {G : Type} [Group G] [Finite G] {p : ℕ} (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hAJ : ggAutomizer J Bs ≠ ⊥)
    (hK1 : GGQTwoK1 p B Bs x D J) {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    {φ ψ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer ⊤ Bs) (hψ : ψ ∈ ggAutomizer K Bs)
    (hD : ∀ b : ↥Bs, (b : G) ∈ D → (((ψ * φ) b : ↥Bs) : G) ∈ D) :
    φ ∈ ggAutomizer (Subgroup.normalizer (ggG0 p B x L D J : Set G)) Bs :=
  ggQ2_finish_of_le hLB hP hS hAJ hK1 hnb (fun k hk => le_ggG0_of_ggNbr hnb hk) hφ hψ hD

theorem ggQ2_yBridge {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K)
    (hDxy : D = Subgroup.closure {x, y}) {φ : MulAut ↥Bs}
    (h : ∃ w' ∈ M.parabL {k | k ≠ M.b}, ∀ v ∈ Submodule.span (ZMod p) {M.xV, M.yV},
      w' (ggLin (p := p) M.model φ v) ∈ Submodule.span (ZMod p) {M.xV, M.yV}) :
    ∃ ψ ∈ ggAutomizer K Bs, ∀ b : ↥Bs, (b : G) ∈ D → (((ψ * φ) b : ↥Bs) : G) ∈ D :=
  ggQ2_bridge M hDxy (by rw [ggQ2_parabL_eq_map, ← M.automizer_K]) h

end CFSG.StandardType

end
