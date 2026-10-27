module

public import CFSG.Quasithin.Recognition.St84.Sec6NatQuot

public section

namespace CFSG.Quasithin.St84

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem relCent_le (E Z A : Subgroup G) : relCent E Z A ≤ E := fun _ hx => hx.1

theorem conj_mem_relCent {E Z A : Subgroup G} {g x : G}
    (hgE : g ∈ Subgroup.normalizer (E : Set G)) (hgZ : g ∈ Subgroup.normalizer (Z : Set G))
    (hgA : g ∈ Subgroup.normalizer (A : Set G)) (hx : x ∈ relCent E Z A) :
    g * x * g⁻¹ ∈ relCent E Z A := by
  obtain ⟨hxE, hxN, hxA⟩ := hx
  refine ⟨(Subgroup.mem_normalizer_iff.mp hgE x).mp hxE,
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hgZ hxN) (Subgroup.inv_mem _ hgZ), fun a ha => ?_⟩
  have ha' : g⁻¹ * a * g ∈ A := by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgA) a).mp ha
    simpa using h
  have h1 := (Subgroup.mem_normalizer_iff.mp hgZ _).mp (hxA _ ha')
  have e : ⁅g * x * g⁻¹, a⁆ = g * ⁅x, g⁻¹ * a * g⁆ * g⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact h1

theorem mem_normalizer_relCent {E Z A : Subgroup G} {g : G}
    (hgE : g ∈ Subgroup.normalizer (E : Set G)) (hgZ : g ∈ Subgroup.normalizer (Z : Set G))
    (hgA : g ∈ Subgroup.normalizer (A : Set G)) :
    g ∈ Subgroup.normalizer (relCent E Z A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_relCent hgE hgZ hgA, fun h => ?_⟩
  have h' := conj_mem_relCent (Subgroup.inv_mem _ hgE) (Subgroup.inv_mem _ hgZ)
    (Subgroup.inv_mem _ hgA) h
  simpa [mul_assoc] using h'

theorem relCent_map_of_injective {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) {E Z C : Subgroup A}
    (hEZ : E ≤ Subgroup.normalizer (Z : Set A)) :
    (relCent E Z C).map f = relCent (E.map f) (Z.map f) (C.map f) := by
  ext u
  constructor
  · rintro ⟨g, ⟨hgE, hgN, hgC⟩, rfl⟩
    refine ⟨⟨g, hgE, rfl⟩, Subgroup.le_normalizer_map f ⟨g, hgN, rfl⟩, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_commutatorElement]
    exact ⟨_, hgC a ha, rfl⟩
  · rintro ⟨⟨g, hgE, rfl⟩, -, hgC⟩
    refine ⟨g, ⟨hgE, hEZ hgE, fun a ha => ?_⟩, rfl⟩
    have h := hgC (f a) ⟨a, ha, rfl⟩
    rw [← map_commutatorElement] at h
    exact (Subgroup.mem_map_iff_mem hf).mp h

end CFSG.Quasithin.St84
