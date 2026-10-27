module

public import CFSG.Quasithin.H13.L32AC48a
public import CFSG.Quasithin.H13.Sp62Over
public import CFSG.Quasithin.EmptyFaithful.S146F3
public import CFSG.Quasithin.H13.L32AC47f

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.Quasithin.H13.L32A.C.Alt6 (conjK conjK_apply)

section SL3

open Matrix

theorem sl3_comm_fact : ∀ g : A6.SL3.S, g ≠ 1 → g ^ 21 = 1 →
    ∃ s ∈ A6.SL3.P0list, (g⁻¹ * s * g * s⁻¹) ^ 4 ≠ 1 := by
  decide +kernel

theorem sl3_two_elt : ∀ g : A6.SL3.S, g ^ 8 = 1 → g ^ 4 = 1 := by
  decide +kernel

theorem sl3_center_fact : ∀ g : A6.SL3.S, g * A6.SL3.ex = A6.SL3.ex * g →
    g * A6.SL3.ey = A6.SL3.ey * g → g * A6.SL3.s1 = A6.SL3.s1 * g →
    g * A6.SL3.s2 = A6.SL3.s2 * g → g = 1 := by
  decide +kernel

theorem sl3_normalizer_P0 : ∀ g : A6.SL3.S,
    (∀ p ∈ A6.SL3.P0list, A6.SL3.InX1 (g * p * g⁻¹) ∧ A6.SL3.InX2 (g * p * g⁻¹)) →
    A6.SL3.InX1 g ∧ A6.SL3.InX2 g := by
  decide +kernel

theorem sl3_center_eq_bot : Subgroup.center A6.SL3.S = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_center_iff] at hg
  exact sl3_center_fact g (hg _).symm (hg _).symm (hg _).symm (hg _).symm

theorem sl3_sup_X : A6.SL3.X1 ⊔ A6.SL3.X2 = ⊤ := by
  obtain ⟨h12, h21⟩ := A6.SL3.X_incomparable
  rcases A6.SL3.overgroups_SL3 (A6.SL3.X1 ⊔ A6.SL3.X2)
      ((show A6.SL3.P0 ≤ A6.SL3.X1 from inf_le_left).trans le_sup_left) with h | h | h | h
  · exact absurd (h ▸ le_sup_left : A6.SL3.X1 ≤ A6.SL3.P0) fun h' =>
      h12 (h'.trans inf_le_right)
  · exact absurd (h ▸ le_sup_right : A6.SL3.X2 ≤ A6.SL3.X1) h21
  · exact absurd (h ▸ le_sup_left : A6.SL3.X1 ≤ A6.SL3.X2) h12
  · exact h

theorem sl3_outer : IsPGroup 2 (Outer A6.SL3.S) := by
  have hP : IsPSL 3 2 1 A6.SL3.S := isPSL_three_two_iff.mpr ⟨MulEquiv.refl _⟩
  have : Finite (MulAut A6.SL3.S) :=
    Finite.of_injective (fun f : MulAut A6.SL3.S => (f : A6.SL3.S → A6.SL3.S))
      DFunLike.coe_injective
  have hb := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    (Or.inl rfl) le_rfl Nat.prime_two le_rfl hP).1
  refine isPGroup_two_outer_of_dvd_two (hb.trans ?_)
  simp [CFSG.RankThree.OuterOrder.determinantParameter]

end SL3

end CFSG.Quasithin.H13.L32A.C
