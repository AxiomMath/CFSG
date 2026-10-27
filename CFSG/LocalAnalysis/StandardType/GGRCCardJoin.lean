module

public import CFSG.LocalAnalysis.StandardType.GGResKnownGroup

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private def l05nK7b_stabEquiv {G : Type*} [Group G] (S A : Subgroup G) :
    ↥(S.subgroupOf A) ≃ ↥(A ⊓ S) where
  toFun x := ⟨((x : ↥A) : G), (x : ↥A).2, x.2⟩
  invFun x := ⟨⟨(x : G), x.2.1⟩, x.2.2⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv x := Subtype.ext rfl

theorem ggRC_card_join_le (hOrb : GGResCentBoundInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hx : x ∈ Bs) :
    Nat.card ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs) ≤
      Nat.card ↥Bs * ((p - 1) * 6 * Nat.card ↥(ggAutomizer L Bs)) := by
  let A' : Subgroup (MulAut ↥Bs) := ggAutomizer L Bs ⊔ ggAutomizer K Bs
  let pt : ↥Bs := ⟨x, hx⟩
  have hstab : Nat.card ↥(MulAction.stabilizer (↥A') pt) ≤
      (p - 1) * 6 * Nat.card ↥(ggAutomizer L Bs) := by
    have hstab_eq : Nat.card ↥(MulAction.stabilizer (↥A') pt) =
        Nat.card ↥(A' ⊓ MulAction.stabilizer (MulAut ↥Bs) pt) := by
      rw [← MulAction.stabilizer_subgroupOf A' pt]
      exact Nat.card_congr
        (l05nK7b_stabEquiv (MulAction.stabilizer (MulAut ↥Bs) pt) A')
    rw [hstab_eq]
    exact hOrb G p B Bs x L D J y K hH hx
  let _ : Fintype ↥A' := Fintype.ofFinite ↥A'
  let _ : Fintype ↥(MulAction.orbit (↥A') pt) := Fintype.ofFinite ↥(MulAction.orbit (↥A') pt)
  let _ : Fintype ↥(MulAction.stabilizer (↥A') pt) :=
    Fintype.ofFinite ↥(MulAction.stabilizer (↥A') pt)
  have hOS := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := ↥A') pt
  simp only [← Nat.card_eq_fintype_card] at hOS
  change Nat.card ↥A' ≤ Nat.card ↥Bs * ((p - 1) * 6 * Nat.card ↥(ggAutomizer L Bs))
  rw [← hOS]
  refine Nat.mul_le_mul ?_ hstab
  exact Nat.card_le_card_of_injective
    (Subtype.val : ↥(MulAction.orbit (↥A') pt) → ↥Bs) Subtype.val_injective

end CFSG.StandardType
