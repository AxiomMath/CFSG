module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.E2P.Asc80

theorem exists_fixed_ne_zero {V : Type*} [AddCommMonoid V] [Finite V] {p : ℕ} [Fact p.Prime]
    {U : Type*} [Group U] [DistribMulAction U V] (hU : IsPGroup p U) (hV : p ∣ Nat.card V) :
    ∃ v : V, v ≠ 0 ∧ ∀ u : U, u • v = v := by
  have hmod := hU.card_modEq_card_fixedPoints V
  have hdvd : p ∣ Nat.card (MulAction.fixedPoints U V) :=
    Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hV))
  have h0 : (0 : V) ∈ MulAction.fixedPoints U V := fun u => smul_zero u
  have hpos : 0 < Nat.card (MulAction.fixedPoints U V) :=
    Nat.card_pos_iff.mpr ⟨⟨⟨0, h0⟩⟩, inferInstance⟩
  have h1 : 1 < Nat.card (MulAction.fixedPoints U V) :=
    lt_of_lt_of_le (Fact.out : p.Prime).one_lt (Nat.le_of_dvd hpos hdvd)
  have : Nontrivial (MulAction.fixedPoints U V) := Finite.one_lt_card_iff_nontrivial.mp h1
  obtain ⟨x, hx⟩ := exists_ne (⟨0, h0⟩ : MulAction.fixedPoints U V)
  refine ⟨x.1, fun h => hx (Subtype.ext h), fun u => x.2 u⟩

end CFSG.Quasithin.E2P.Asc80
