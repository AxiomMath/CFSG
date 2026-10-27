module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_16

namespace CFSG
end CFSG
open CFSG

/-!
# A generalized-Fitting criterion for a self-centralizing p-core

If the generalized Fitting subgroup of an ambient subgroup `A` is a
`p`-group, then the `p`-core of the abstract group `A` is self-centralizing.
This is the centralizer hypothesis needed to apply Glauberman's Theorem A.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- If `F*(A)` is a `p`-group, then `C_A(O_p(A)) ≤ O_p(A)`. -/
public theorem centralizer_pCore_le_of_generalizedFitting_isPGroup
    {G : Type u} [Group G] [Finite G]
    (A : Subgroup G) {p : ℕ} (hp : p.Prime)
    (hAp : IsPGroup p (generalizedFittingSubgroupOf A)) :
    Subgroup.centralizer ((pCore p (↥A) : Subgroup (↥A)) : Set (↥A)) ≤
      pCore p (↥A) := by
  have hEbot : componentLayerOf A = ⊥ :=
    componentLayerOf_eq_bot_of_isPGroup A hp hAp
  have hFstar_eq_fit : generalizedFittingSubgroupOf A = fittingSubgroupOf A := by
    simp [generalizedFittingSubgroupOf, hEbot]
  have hfit_eq_core : fittingSubgroupOf A = qCoreOf A p :=
    (qCoreOf_eq_fittingSubgroupOf_of_isPGroup A hp hAp).symm
  have hFstar_eq_core :
      generalizedFittingSubgroupOf A = (pCore p (↥A)).map A.subtype := by
    rw [hFstar_eq_fit, hfit_eq_core]
    rfl
  intro x hx
  have hxC : (x : G) ∈
      Subgroup.centralizer ((generalizedFittingSubgroupOf A : Set G)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [hFstar_eq_core] at hy
    rcases Subgroup.mem_map.mp hy with ⟨yA, hycore, rfl⟩
    have hcomm := (Subgroup.mem_centralizer_iff.mp hx) yA hycore
    exact congrArg Subtype.val hcomm
  have hxFstar : (x : G) ∈ generalizedFittingSubgroupOf A :=
    centralizer_intersection_fstar_le_fstar A ⟨hxC, x.property⟩
  rw [hFstar_eq_core] at hxFstar
  rcases Subgroup.mem_map.mp hxFstar with ⟨y, hy, hxy⟩
  have hxyA : y = x := Subtype.ext hxy
  simpa [hxyA] using hy

end CFSG.GorensteinWalter
