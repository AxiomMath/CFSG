module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.St84

open scoped commutatorElement

open CFSG.QuasithinUnique

variable {G : Type*} [Group G]

@[expose] def relCent (E Z A : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ E ∧ g ∈ Subgroup.normalizer (Z : Set G) ∧
    ∀ a ∈ A, ⁅g, a⁆ ∈ Z}
  one_mem' := by
    refine ⟨E.one_mem, Subgroup.one_mem _, fun a _ => ?_⟩
    simp
  mul_mem' := by
    rintro g h ⟨hgE, hgN, hg⟩ ⟨hhE, hhN, hh⟩
    refine ⟨E.mul_mem hgE hhE, Subgroup.mul_mem _ hgN hhN, fun a ha => ?_⟩
    have e : ⁅g * h, a⁆ = g * ⁅h, a⁆ * g⁻¹ * ⁅g, a⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Z.mul_mem ((Subgroup.mem_normalizer_iff.mp hgN _).mp (hh a ha)) (hg a ha)
  inv_mem' := by
    rintro g ⟨hgE, hgN, hg⟩
    refine ⟨E.inv_mem hgE, Subgroup.inv_mem _ hgN, fun a ha => ?_⟩
    have h1 : ⁅g, a⁆ ∈ Z := hg a ha
    have e : ⁅g⁻¹, a⁆ = g⁻¹ * ⁅g, a⁆⁻¹ * g := by
      simp only [commutatorElement_def]
      group
    rw [e]
    simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgN) _).mp (Z.inv_mem h1)

theorem mem_relCent {E Z A : Subgroup G} (hEZ : E ≤ Subgroup.normalizer (Z : Set G)) {g : G} :
    g ∈ relCent E Z A ↔ g ∈ E ∧ ∀ a ∈ A, ⁅g, a⁆ ∈ Z := by
  constructor
  · rintro ⟨hgE, -, hg⟩
    exact ⟨hgE, hg⟩
  · rintro ⟨hgE, hg⟩
    exact ⟨hgE, hEZ hgE, hg⟩

structure NatQuot (L E Z : Subgroup G) (n : ℕ) : Prop where
  Z_le : Z ≤ E
  E_le : E ≤ L
  normal : L ≤ Subgroup.normalizer (E : Set G) ⊓ Subgroup.normalizer (Z : Set G)
  index : Z.relIndex E = 2 ^ (2 * n)
  line : ∀ A : Subgroup G, IsSylowTwoOf A L →
    Z.relIndex (relCent E Z A) = 2 ^ n
  comm_eq : ∀ A : Subgroup G, IsSylowTwoOf A L → ⁅E, A⁆ ⊔ Z = relCent E Z A
  lines_inf : ∀ A A' : Subgroup G, IsSylowTwoOf A L → IsSylowTwoOf A' L →
    ¬ A ≤ A' ⊔ E → relCent E Z A ⊓ relCent E Z A' = Z ∧
      relCent E Z A ⊔ relCent E Z A' = E
  fpf : ∀ g ∈ L, Odd (orderOf g) → g ∉ E → ∀ e ∈ E, ⁅e, g⁆ ∈ Z → e ∈ Z
  irred : ∀ A : Subgroup G, Z ≤ A → A ≤ E → L ≤ Subgroup.normalizer (A : Set G) →
    A = Z ∨ A = E

end CFSG.Quasithin.St84
