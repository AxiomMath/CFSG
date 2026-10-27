module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.Index

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace Converse

/-! ### Orbit–stabilizer in a doubly transitive action -/

/-- Orbit–stabilizer, in `Nat.card` form. -/
public theorem card_stabilizer_mul_card_orbit {G X : Type*} [Group G] [MulAction G X]
    [Finite G] (b : X) :
    Nat.card (MulAction.stabilizer G b) * Nat.card (MulAction.orbit G b) = Nat.card G := by
  rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer G b)]
  exact Subgroup.card_mul_index _

/-- In a doubly transitive action of a finite group, a one-point stabilizer has
order `|Ω| - 1` times the order of a two-point stabilizer: the stabilizer of `a`
is transitive on the remaining points. -/
public theorem card_stabilizer_eq_twoPoint_mul
    {K Ω : Type*} [Group K] [Finite K] [MulAction K Ω] [Finite Ω]
    (h2 : MulAction.IsMultiplyPretransitive K Ω 2) {a b : Ω} (hba : b ≠ a) :
    Nat.card (MulAction.stabilizer K a) =
      Nat.card ((MulAction.stabilizer K a ⊓ MulAction.stabilizer K b : Subgroup K)) *
        (Nat.card Ω - 1) := by
  classical
  haveI : Fintype Ω := Fintype.ofFinite _
  have h2' : ∀ {x y z w : Ω}, x ≠ y → z ≠ w → ∃ g : K, g • x = z ∧ g • y = w :=
    MulAction.is_two_pretransitive_iff.1 h2
  have horb : MulAction.orbit (MulAction.stabilizer K a) b = {z : Ω | z ≠ a} := by
    ext z
    constructor
    · rintro ⟨h, rfl⟩
      intro hcon
      apply hba
      have hfix : (h : K) • a = a := h.2
      have hcon' : (h : K) • b = a := hcon
      have hinvfix : ((h : K))⁻¹ • a = a := inv_smul_eq_iff.2 hfix.symm
      have h1 : ((h : K))⁻¹ • ((h : K) • b) = ((h : K))⁻¹ • a := by rw [hcon']
      rw [inv_smul_smul] at h1
      rw [h1]
      exact hinvfix
    · intro hz
      obtain ⟨g, hg1, hg2⟩ := @h2' a b a z (Ne.symm hba) (Ne.symm hz)
      exact ⟨⟨g, hg1⟩, hg2⟩
  have hstabeq : MulAction.stabilizer (MulAction.stabilizer K a) b =
      (MulAction.stabilizer K a ⊓ MulAction.stabilizer K b).subgroupOf
        (MulAction.stabilizer K a) := by
    ext x
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
  have h := card_stabilizer_mul_card_orbit (G := MulAction.stabilizer K a) b
  rw [hstabeq, horb,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : MulAction.stabilizer K a ⊓ MulAction.stabilizer K b ≤
        MulAction.stabilizer K a)).toEquiv] at h
  have hcompl : Nat.card {z : Ω | z ≠ a} = Nat.card Ω - 1 := by
    show Nat.card {z : Ω // ¬ (z = a)} = Nat.card Ω - 1
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
      ← Nat.card_eq_fintype_card]
  rw [hcompl] at h
  exact h.symm

end Converse
end CFSG.BenderSuzuki
