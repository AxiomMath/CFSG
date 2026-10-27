module

public import CFSG.RankThree.GF2n.Tim79aSec22Comm
public import CFSG.RankThree.GF2n.Tim79aSec22Class

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G]

structure Sec2 (M V Q P H : Subgroup G) : Prop extends MinCex M V Q P H where
  centralizer_P : Subgroup.centralizer (P : Set G) = V
  frattini_P : inSubgroup frattini P ≤ V
  eV_ne_bot : eOf H ⊓ V ≠ ⊥
  w_elem : Assembly.IsElemAbelian 2 (wOf V H)
  fitting_X : generalizedFitting ↥(xOf V H) = pCore 2 ↥(xOf V H)
  fitting_central : ∀ x ∈ barOf V H (inSubgroup generalizedFitting (xOf V H)),
    ∀ y ∈ barOf V H (xOf V H), x * y = y * x
  dbar_root : CFSG.Timmesfeld.IsRootInvolutionSet (dbarOf V H)
  commute_of_isPGroup : ∀ h ∈ H, IsPGroup 2 ↥(barOf V H V ⊔ barOf V H (conjSubgroup h V)) →
    ∀ u ∈ V, ∀ v ∈ conjSubgroup h V, u * v = v * u
  ti_bar : IsTI (barOf V H V)
  normalizer_bar : Subgroup.normalizer ((barOf V H V : Subgroup (Hbar V H)) : Set (Hbar V H)) =
    barOf V H (Subgroup.normalizer (V : Set G))
  centralizer_w : wOf V H ⊓ Subgroup.centralizer (xOf V H : Set G) = ⊥
  commutator_w : ⁅wOf V H, xOf V H⁆ = wOf V H
  class_dbar : ∃ d₀ ∈ dbarOf V H, ∀ y : Hbar V H,
    y ∈ dbarOf V H ↔ ∃ x ∈ barOf V H (xOf V H), y = x * d₀ * x⁻¹
  H_eq : xOf V H ⊔ P = H
  closure_dbar : Subgroup.closure (dbarOf V H) = barOf V H (xOf V H)

variable {M V Q P H : Subgroup G} [Finite G]

theorem MinCex.sec2 (hc : MinCex M V Q P H) : Sec2 M V Q P H :=
  { toMinCex := hc
    centralizer_P := hc.centralizer_P_eq
    frattini_P := hc.frattini_P_le
    eV_ne_bot := hc.eOf_inf_V_ne_bot
    w_elem := hc.wOf_isElemAbelian
    fitting_X := hc.fitting_xOf
    fitting_central := hc.fitting_xOf_central_bar
    dbar_root := hc.dbarOf_isRootInvolutionSet
    commute_of_isPGroup := fun _ hh h2 => hc.commute_of_isPGroup_barOf_sup hh h2
    ti_bar := hc.isTI_barOf_V
    normalizer_bar := hc.normalizer_barOf_V
    centralizer_w := hc.wOf_inf_centralizer_xOf_eq_bot
    commutator_w := hc.commutator_wOf_xOf
    class_dbar := hc.dbarOf_isClass
    H_eq := hc.xOf_sup_P_eq_H
    closure_dbar := hc.closure_dbarOf }

end CFSG.RankThree.GF2n.Tim79a
