module

public import CFSG.LocalAnalysis.StandardType.GGQTwoReflCut

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private def ggQ2s08b3a_stabEquiv {G : Type*} [Group G] (S A : Subgroup G) :
    ↥(S.subgroupOf A) ≃ ↥(A ⊓ S) where
  toFun x := ⟨((x : ↥A) : G), (x : ↥A).2, x.2⟩
  invFun x := ⟨⟨(x : G), x.2.1⟩, x.2.2⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv x := Subtype.ext rfl

theorem ggQ2s08_card_le_of_stab {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {x : G}
    (hx : x ∈ Bs) {S : ℕ}
    (hstab : Nat.card ↥(ggAutomizer ⊤ Bs ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs)) ≤ S)
    {A : Subgroup (MulAut ↥Bs)} (hA : A ≤ ggAutomizer ⊤ Bs) :
    Nat.card ↥A ≤ Nat.card ↥Bs * S := by
  let pt : ↥Bs := ⟨x, hx⟩
  have hstab_A : Nat.card ↥(MulAction.stabilizer (↥A) pt) ≤ S := by
    have hstab_eq : Nat.card ↥(MulAction.stabilizer (↥A) pt) =
        Nat.card ↥(A ⊓ MulAction.stabilizer (MulAut ↥Bs) pt) := by
      rw [← MulAction.stabilizer_subgroupOf A pt]
      exact Nat.card_congr
        (ggQ2s08b3a_stabEquiv (MulAction.stabilizer (MulAut ↥Bs) pt) A)
    rw [hstab_eq]
    exact le_trans
      (Subgroup.card_le_of_le (le_inf (le_trans inf_le_left hA) inf_le_right)) hstab
  let _ : Fintype ↥A := Fintype.ofFinite ↥A
  let _ : Fintype ↥(MulAction.orbit (↥A) pt) := Fintype.ofFinite ↥(MulAction.orbit (↥A) pt)
  let _ : Fintype ↥(MulAction.stabilizer (↥A) pt) :=
    Fintype.ofFinite ↥(MulAction.stabilizer (↥A) pt)
  have hOS := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := ↥A) pt
  simp only [← Nat.card_eq_fintype_card] at hOS
  change Nat.card ↥A ≤ Nat.card ↥Bs * S
  rw [← hOS]
  refine Nat.mul_le_mul ?_ hstab_A
  exact Nat.card_le_card_of_injective
    (Subtype.val : ↥(MulAction.orbit (↥A) pt) → ↥Bs) Subtype.val_injective

end CFSG.StandardType

end
