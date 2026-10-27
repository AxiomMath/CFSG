module

public import CFSG.LocalAnalysis.StandardType.GGQTwoReflCut

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private def ggQ2s08b3b_stabEquiv {G : Type*} [Group G] (S A : Subgroup G) :
    ↥(S.subgroupOf A) ≃ ↥(A ⊓ S) where
  toFun x := ⟨((x : ↥A) : G), (x : ↥A).2, x.2⟩
  invFun x := ⟨⟨(x : G), x.2.1⟩, x.2.2⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv x := Subtype.ext rfl

theorem ggQ2s08_card_le_of_stab_red {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {x : G}
    (hx : x ∈ Bs) (hab : ∀ a b : ↥Bs, a * b = b * a) {S : ℕ}
    (hstab : Nat.card ↥(ggAutomizer ⊤ Bs ⊓ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hx⟩ : ↥Bs)) ≤ S)
    {A : Subgroup (MulAut ↥Bs)} (hA : A ≤ ggAutomizer ⊤ Bs) {H : Subgroup ↥Bs}
    (hxH : (⟨x, hx⟩ : ↥Bs) ∉ H) (hidx : H.index = 3) (hinv : ∀ φ ∈ A, ∀ b ∈ H, φ b ∈ H) :
    Nat.card ↥A ≤ 2 * Nat.card ↥H * S := by
  classical
  let b : ↥Bs := ⟨x, hx⟩
  have hnotH : ∀ φ : ↥A, (φ : MulAut ↥Bs) b ∉ H := by
    intro φ hφH
    have hmem : (φ : MulAut ↥Bs)⁻¹ ∈ A := A.inv_mem φ.2
    have h2 := hinv ((φ : MulAut ↥Bs)⁻¹) hmem ((φ : MulAut ↥Bs) b) hφH
    rw [show (φ : MulAut ↥Bs)⁻¹ ((φ : MulAut ↥Bs) b) = b by simp] at h2
    exact hxH h2
  have horb_sub : MulAction.orbit (↥A) b ⊆ {p : ↥Bs | p ∉ H} := by
    intro p hp
    rw [MulAction.mem_orbit_iff] at hp
    obtain ⟨φ, hφp⟩ := hp
    rw [← hφp]
    change (φ : MulAut ↥Bs) b ∉ H
    exact hnotH φ
  have hcard : Nat.card ↥Bs = Nat.card ↥H * 3 := by
    have h3 := Subgroup.card_mul_index H
    rw [hidx] at h3
    exact h3.symm
  have hcomp : ({p : ↥Bs | p ∉ H}).ncard = 2 * Nat.card ↥H := by
    have h3 : ({p : ↥Bs | p ∉ H}).ncard = (H : Set ↥Bs)ᶜ.ncard := rfl
    have hcoen : (H : Set ↥Bs).ncard = Nat.card ↥H :=
      (Nat.card_coe_set_eq (H : Set ↥Bs)).symm
    rw [h3, Set.ncard_compl, hcoen, hcard]
    omega
  have horbcard : Nat.card ↥(MulAction.orbit (↥A) b) ≤ 2 * Nat.card ↥H := by
    rw [Nat.card_coe_set_eq]
    exact le_trans (Set.ncard_le_ncard horb_sub) (le_of_eq hcomp)
  have hstabA : Nat.card ↥(MulAction.stabilizer (↥A) b) ≤ S := by
    have h1 : Nat.card ↥(MulAction.stabilizer (↥A) b) =
        Nat.card ↥(A ⊓ MulAction.stabilizer (MulAut ↥Bs) b) := by
      rw [← MulAction.stabilizer_subgroupOf A b]
      exact Nat.card_congr (ggQ2s08b3b_stabEquiv (MulAction.stabilizer (MulAut ↥Bs) b) A)
    rw [h1]
    refine le_trans ?_ hstab
    refine Nat.card_le_card_of_injective
      (fun x : ↥(A ⊓ MulAction.stabilizer (MulAut ↥Bs) b) =>
        (⟨(x : MulAut ↥Bs), hA x.2.1, x.2.2⟩ :
          ↥(ggAutomizer ⊤ Bs ⊓ MulAction.stabilizer (MulAut ↥Bs) b))) ?_
    intro x y hxy
    exact Subtype.ext (congrArg
      (fun z : ↥(ggAutomizer ⊤ Bs ⊓ MulAction.stabilizer (MulAut ↥Bs) b) =>
        (z : MulAut ↥Bs)) hxy)
  let _ : Fintype ↥A := Fintype.ofFinite ↥A
  let _ : Fintype ↥(MulAction.orbit (↥A) b) := Fintype.ofFinite ↥(MulAction.orbit (↥A) b)
  let _ : Fintype ↥(MulAction.stabilizer (↥A) b) :=
    Fintype.ofFinite ↥(MulAction.stabilizer (↥A) b)
  have hOS := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := ↥A) b
  simp only [← Nat.card_eq_fintype_card] at hOS
  rw [← hOS]
  exact Nat.mul_le_mul horbcard hstabA

end CFSG.StandardType

end
