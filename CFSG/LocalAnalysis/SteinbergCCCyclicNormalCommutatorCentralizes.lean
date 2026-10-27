module

public import Mathlib.Tactic.Group
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.LocalAnalysis

namespace CyclicNormalConj

open scoped commutatorElement

variable {E : Type*} [Group E] {X : Subgroup E}

theorem exists_zpow_of_isCyclic [X.Normal] (hX : IsCyclic X) (e : E) :
    ∃ a : ℤ, ∀ y ∈ X, e * y * e⁻¹ = y ^ a := by
  obtain ⟨g, hg⟩ := hX.exists_generator
  have hge : e * (g : E) * e⁻¹ ∈ X := Subgroup.Normal.conj_mem inferInstance _ g.2 e
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨_, hge⟩)
  have ha' : (g : E) ^ a = e * (g : E) * e⁻¹ := by
    have := congrArg Subtype.val ha
    simpa using this
  refine ⟨a, fun y hy => ?_⟩
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
  have hm' : (g : E) ^ m = y := by
    have := congrArg Subtype.val hm
    simpa using this
  rw [← hm', ← zpow_mul, mul_comm, zpow_mul, ha', ← conj_zpow]

theorem conj_conj_comm [X.Normal] (hX : IsCyclic X) (e₁ e₂ : E) {y : E} (hy : y ∈ X) :
    e₁ * (e₂ * y * e₂⁻¹) * e₁⁻¹ = e₂ * (e₁ * y * e₁⁻¹) * e₂⁻¹ := by
  obtain ⟨a₁, ha₁⟩ := exists_zpow_of_isCyclic hX e₁
  obtain ⟨a₂, ha₂⟩ := exists_zpow_of_isCyclic hX e₂
  rw [ha₂ y hy, ha₁ y hy, ha₁ _ (zpow_mem hy a₂), ha₂ _ (zpow_mem hy a₁), ← zpow_mul, ← zpow_mul,
    mul_comm]

theorem commutatorElement_conj [X.Normal] (hX : IsCyclic X) (e₁ e₂ : E) {y : E} (hy : y ∈ X) :
    ⁅e₁, e₂⁆ * y * ⁅e₁, e₂⁆⁻¹ = y := by
  have h1 := conj_conj_comm hX e₁⁻¹ e₂⁻¹ hy
  rw [inv_inv, inv_inv] at h1
  rw [commutatorElement_def]
  calc e₁ * e₂ * e₁⁻¹ * e₂⁻¹ * y * (e₁ * e₂ * e₁⁻¹ * e₂⁻¹)⁻¹ =
      e₁ * e₂ * (e₁⁻¹ * (e₂⁻¹ * y * e₂) * e₁) * e₂⁻¹ * e₁⁻¹ := by group
    _ = e₁ * e₂ * (e₂⁻¹ * (e₁⁻¹ * y * e₁) * e₂) * e₂⁻¹ * e₁⁻¹ := by rw [h1]
    _ = y := by group

theorem commutator_le_centralizer [X.Normal] (hX : IsCyclic X) :
    commutator E ≤ Subgroup.centralizer (X : Set E) := by
  rw [commutator_def, Subgroup.commutator_le]
  intro e₁ _ e₂ _
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 := commutatorElement_conj hX e₁ e₂ hy
  calc y * ⁅e₁, e₂⁆ = ⁅e₁, e₂⁆ * y * ⁅e₁, e₂⁆⁻¹ * ⁅e₁, e₂⁆ := by rw [h1]
    _ = ⁅e₁, e₂⁆ * y := by group

theorem le_centralizer_of_perfect [X.Normal] (hX : IsCyclic X) {P : Subgroup E}
    (hP : ⁅P, P⁆ = P) : P ≤ Subgroup.centralizer (X : Set E) := by
  rw [← hP]
  exact (Subgroup.commutator_mono le_top le_top).trans (commutator_le_centralizer hX)

end CyclicNormalConj

end CFSG.LocalAnalysis
