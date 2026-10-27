module

public import CFSG.Quasithin.H13.A5Rows
public import CFSG.Quasithin.H13.A5Facts1321b
public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationTwelveOut
public import CFSG.Quasithin.Background.HL42Aut
public import CFSG.Quasithin.H13.VolIAutSLFive

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms

theorem mem_inner_of_pow_three_of_card_le {X : Type*} [Group X] [Finite X]
    (hZ : Subgroup.center X = ⊥) (hA : Nat.card (MulAut X) ≤ 2 * Nat.card X) {α : MulAut X}
    (h3 : α ^ 3 = 1) : α ∈ inner X := by
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := by
    refine (MonoidHom.ker_eq_bot_iff _).mp ((Subgroup.eq_bot_iff_forall _).2 fun g hg => ?_)
    have hcen : g ∈ Subgroup.center X := by
      refine Subgroup.mem_center_iff.mpr fun y => ?_
      have h1 := congrArg (fun φ : MulAut X => φ y) (MonoidHom.mem_ker.mp hg)
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc y * g = (g * y * g⁻¹) * g := by rw [h1]
        _ = g * y := by group
    rwa [hZ, Subgroup.mem_bot] at hcen
  have hinn : Nat.card (inner X) = Nat.card X :=
    (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have : Finite (MulAut X) :=
    Finite.of_injective (fun f : MulAut X => (f : X → X)) DFunLike.coe_injective
  have hidx := (inner X).index_mul_card
  rw [hinn] at hidx
  have hpos : 0 < Nat.card X := Nat.card_pos
  have hle : (inner X).index ≤ 2 := by
    have h1 : (inner X).index * Nat.card X ≤ 2 * Nat.card X := hidx ▸ hA
    exact Nat.le_of_mul_le_mul_right h1 hpos
  have hne : (inner X).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hmem := (inner X).pow_index_mem α
  obtain h | h : (inner X).index = 1 ∨ (inner X).index = 2 := by omega
  · rwa [h, pow_one] at hmem
  · rw [h] at hmem
    have hα : α = α ^ 3 * (α ^ 2)⁻¹ := by group
    rw [hα, h3, one_mul]
    exact (inner X).inv_mem hmem

theorem mem_inner_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : ∀ β : MulAut Y, β ^ 3 = 1 → β ∈ inner Y) {α : MulAut X} (hα : α ^ 3 = 1) :
    α ∈ inner X := by
  have h1 : MulAut.congr e α ∈ inner Y := h _ (by rw [← map_pow, hα, map_one])
  rw [← inner_map_congr e] at h1
  exact (Subgroup.mem_map_iff_mem (f := (MulAut.congr e).toMonoidHom)
    (MulAut.congr e).injective).mp h1

theorem center_sl_two_eq_bot (n : ℕ) [NeZero n] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) = ⊥ := by
  refine center_sl_eq_bot fun r hr => ?_
  have h01 : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide
  rcases h01 r with rfl | rfl
  · rw [zero_pow (NeZero.ne n)] at hr
    exact absurd hr (by decide)
  · rfl

theorem RowType.mem_inner
    {X : Type} [Group X] [Finite X] (h : RowType X) {α : MulAut X}
    (hα : α ^ 3 = 1) : α ∈ inner X := by
  rcases h with h | h | h | h <;> obtain ⟨e⟩ := h
  · exact A10.mem_inner_of_pow_three e hα
  · exact mem_inner_of_mulEquiv e (fun β hβ => mem_inner_of_pow_three_of_card_le
      (center_sl_two_eq_bot 4) H.L4.card_mulAut_SL_four hβ) hα
  · exact mem_inner_of_mulEquiv e (fun β hβ => mem_inner_of_pow_three_of_card_le
      (center_sl_two_eq_bot 5) VolI.autSLFiveTwo_holds hβ) hα
  · have : Finite U33G := u33Pres_finite_card_le.1
    exact mem_inner_of_mulEquiv e (fun β hβ => mem_inner_of_pow_three_of_card_le
      center_u33Pres_eq_bot (by rw [card_u33Pres]; exact card_mulAut_u33Pres_le) hβ) hα

theorem factOutRows1321
    : FactOutRows1321 := by
  intro V _ _ hV G L A hB4 hrow α hα
  obtain ⟨l, hl⟩ := (rowType_of_rows hV hB4 hrow).mem_inner hα
  exact ⟨l, hl.symm⟩

end CFSG.Quasithin.H13.A5
