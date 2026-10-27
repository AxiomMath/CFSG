module

public import CFSG.LocalAnalysis.StandardType.GGE6RankFiveTorality

public noncomputable section
namespace CFSG.LieType.AlgebraicGroups
open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
variable {k : Type} [Field k] [IsAlgClosed k]


open scoped Pointwise in
theorem mem_of_mem_original_centralizer_of_cube_eq_one
    [CharP k 2]
    {E : Subgroup (ModGL .E6 k)} [Finite E]
    (hEG : E ≤ adjointGroup .E6 k) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hNT : ¬ CFSG.StandardType.SCFourCover.E6AdToral E)
    {x : ModGL .E6 k} (hx : x ∈ adjointGroup .E6 k ⊓ centralizer (E : Set (ModGL .E6 k)))
    (hx3 : x ^ 3 = 1) : x ∈ E := by
  let F := E ⊔ zpowers x
  have hxfin : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by decide, hx3⟩
  let : Finite (zpowers x) := finite_zpowers.mpr hxfin
  have hnorm : zpowers x ≤ normalizer (E : Set (ModGL .E6 k)) :=
    zpowers_le.mpr (centralizer_le_normalizer E hx.2)
  let : Finite F := by
    apply Set.Finite.to_subtype
    change ((E ⊔ zpowers x : Subgroup (ModGL .E6 k)) : Set (ModGL .E6 k)).Finite
    rw [sup_comm, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm]
    exact (Set.toFinite (zpowers x : Set (ModGL .E6 k))).mul
      (Set.toFinite (E : Set (ModGL .E6 k)))
  have hF : CFSG.Open.IsElemAbelian 3 F := hE.sup_of_commute
    (CFSG.Open.isElemAbelian_zpowers hx3) fun a ha b hb => by
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hb
      exact (show Commute a x from mem_centralizer_iff.mp hx.2 a ha).zpow_right m
  have hFG : F ≤ adjointGroup .E6 k :=
    sup_le hEG (zpowers_le.mpr hx.1)
  have heq : E = F := CFSG.StandardType.E6RankFive.eq_of_le_of_card_four_of_not_e6AdToral
    hFG hF le_sup_left hcard hNT
  rw [heq]
  exact (le_sup_right : zpowers x ≤ F) (mem_zpowers x)


end CFSG.LieType.AlgebraicGroups
