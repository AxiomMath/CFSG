module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.MinimalCounterexample
import Mathlib.GroupTheory.Subgroup.Simple

namespace CFSG
end CFSG
open CFSG

/-!
# GW 1965 Proposition 9 remark: a normal Klein-four subgroup embeds `G` in `S₄`

This module proves the remark from `refs/bender-dihedral-sylow.tex` L158:
if `H` is a normal Klein-four subgroup of a minimal counterexample `G`, then
`G` embeds into `Equiv.Perm (Fin 4)`.

Route: the minimal counterexample is simple (`minimalCounterexample_isSimple`),
so the nontrivial normal subgroup `H` is all of `G`.  Hence `Nat.card G = 4`,
and the left regular action gives an injective homomorphism
`G →* Equiv.Perm G ≃* Equiv.Perm (Fin 4)`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- A normal Klein-four subgroup of a minimal counterexample embeds the
ambient group into the symmetric group on four points. -/
public theorem gw_prop9_fourGroup_normal_subgroup_embeds_S4
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (H : Subgroup G) (hHnormal : H.Normal) (hH : IsKleinFour H) :
    ∃ φ : G →* Equiv.Perm (Fin 4), Function.Injective φ := by
  have hsimple : IsSimpleGroup G := minimalCounterexample_isSimple hmin
  have hHne : H ≠ ⊥ := by
    intro hHbot
    have hcard : Nat.card (↥H) = 4 := hH.card_four
    rw [hHbot] at hcard
    norm_num at hcard
  have hHtop : H = ⊤ := by
    rcases (haveI := hHnormal; hsimple.eq_bot_or_eq_top_of_normal H) with hbot | htop
    · exact False.elim (hHne hbot)
    · exact htop
  have hGcard : Nat.card G = 4 := by
    have eHG : H ≃* G :=
      (MulEquiv.subgroupCongr hHtop).trans (Subgroup.topEquiv (G := G))
    calc
      Nat.card G = Nat.card (↥H) := (Nat.card_congr eHG.toEquiv).symm
      _ = 4 := hH.card_four
  let e : G ≃ Fin 4 := Finite.equivFinOfCardEq hGcard
  let φ : G →* Equiv.Perm (Fin 4) :=
    e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G G)
  refine ⟨φ, ?_⟩
  exact e.permCongrHom.injective.comp (MulAction.toPerm_injective (α := G))

end CFSG.GorensteinWalter
