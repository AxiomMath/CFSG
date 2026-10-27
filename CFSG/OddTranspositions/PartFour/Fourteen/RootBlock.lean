module

public import CFSG.OddTranspositions.Blocks

public section

namespace CFSG.OddTranspositions.PartFour

variable {X : Type} [Group X]

@[expose] def rootBlock (E : Set X) (s : X) : Set X :=
  {t ∈ E | ∀ u ∈ E, Commute u t ↔ Commute u s}

theorem rootBlock_subset (E : Set X) (s : X) : rootBlock E s ⊆ E := fun _ h => h.1

theorem mem_rootBlock_self {E : Set X} {s : X} (hs : s ∈ E) : s ∈ rootBlock E s :=
  ⟨hs, fun _ _ => Iff.rfl⟩

theorem rootBlock_eq_of_mem {E : Set X} {s t : X} (ht : t ∈ rootBlock E s) :
    rootBlock E t = rootBlock E s := by
  ext x
  constructor
  · rintro ⟨hx, hxt⟩
    exact ⟨hx, fun u hu => (hxt u hu).trans (ht.2 u hu)⟩
  · rintro ⟨hx, hxs⟩
    exact ⟨hx, fun u hu => (hxs u hu).trans (ht.2 u hu).symm⟩

theorem image_conj_rootBlock {E : Set X} (hE : ∀ g : X, ∀ x ∈ E, g * x * g⁻¹ ∈ E) (g s : X) :
    (fun x => g * x * g⁻¹) '' rootBlock E s = rootBlock E (g * s * g⁻¹) := by
  have hcomm : ∀ a b : X, Commute (g * a * g⁻¹) (g * b * g⁻¹) ↔ Commute a b := fun a b => by
    constructor
    · intro h
      have := h.conj g⁻¹
      simpa [mul_assoc] using this
    · exact fun h => h.conj g
  ext x
  constructor
  · rintro ⟨y, ⟨hy, hys⟩, rfl⟩
    refine ⟨hE g y hy, fun u hu => ?_⟩
    have hu' : g⁻¹ * u * g⁻¹⁻¹ ∈ E := hE g⁻¹ u hu
    have h1 := hys _ hu'
    have hu'' : g * (g⁻¹ * u * g⁻¹⁻¹) * g⁻¹ = u := by group
    rw [← hcomm, ← hcomm (g⁻¹ * u * g⁻¹⁻¹) s, hu''] at h1
    exact h1
  · rintro ⟨hx, hxs⟩
    refine ⟨g⁻¹ * x * g⁻¹⁻¹, ⟨hE g⁻¹ x hx, fun u hu => ?_⟩, by group⟩
    have h1 := hxs (g * u * g⁻¹) (hE g u hu)
    have hx' : g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x := by group
    rw [← hx', hcomm, hcomm] at h1
    exact h1

theorem isBlock_rootBlock {E : Set X} (hE : ∀ g : X, ∀ x ∈ E, g * x * g⁻¹ ∈ E) {s : X}
    (hs : s ∈ E) (hne : rootBlock E s ≠ E) : IsBlock E (rootBlock E s) := by
  refine ⟨rootBlock_subset E s, ⟨s, mem_rootBlock_self hs⟩, hne, fun g hg => ?_⟩
  rw [image_conj_rootBlock hE g s]
  rw [Set.disjoint_left]
  intro t ht ht'
  apply hg
  have h1 : rootBlock E (g * s * g⁻¹) = rootBlock E s := by
    rw [← rootBlock_eq_of_mem ht', rootBlock_eq_of_mem ht]
  rw [Subgroup.mem_normalizer_iff_conj_image_eq]
  have h2 : (MulAut.conj g : X → X) = fun x => g * x * g⁻¹ := by
    funext x
    rfl
  rw [h2, image_conj_rootBlock hE g s, h1]

theorem commute_of_mem_rootBlock {E : Set X} {s t t' : X} (hs : s ∈ E) (ht : t ∈ rootBlock E s)
    (ht' : t' ∈ rootBlock E s) : Commute t t' :=
  ((ht.2 t' ht'.1).mpr ((ht'.2 s hs).mpr (Commute.refl s)).symm).symm

theorem exists_not_commute_of_rootBlock_ne {E : Set X} (hcls : ∃ d₀ : X, E = {g | IsConj d₀ g})
    {s : X} (hs : s ∈ E) (hne : rootBlock E s ≠ E) : ∀ x ∈ E, ∃ y ∈ E, ¬ Commute x y := by
  obtain ⟨d₀, rfl⟩ := hcls
  have hconj : ∀ (g : X) {a b : X}, Commute a b → Commute (g * a * g⁻¹) (g * b * g⁻¹) :=
    fun g _ _ h => h.conj g
  have hmem : ∀ (g : X) {y : X}, IsConj d₀ y → IsConj d₀ (g * y * g⁻¹) :=
    fun g _ hy => hy.trans (isConj_iff.mpr ⟨g, rfl⟩)
  have hall : (∃ x ∈ {g | IsConj d₀ g}, ∀ y ∈ {g | IsConj d₀ g}, Commute x y) →
      ∀ a ∈ {g | IsConj d₀ g}, ∀ b ∈ {g | IsConj d₀ g}, Commute a b := by
    rintro ⟨x, hx, hxc⟩ a ha b hb
    obtain ⟨g, rfl⟩ := isConj_iff.mp ((isConj_comm.mp hx).trans ha)
    have h1 := hconj g (hxc (g⁻¹ * b * g⁻¹⁻¹) (hmem g⁻¹ hb))
    have h2 : g * (g⁻¹ * b * g⁻¹⁻¹) * g⁻¹ = b := by group
    rwa [h2] at h1
  by_contra h
  push Not at h
  apply hne
  ext t
  refine ⟨fun ht => ht.1, fun ht => ⟨ht, fun u hu => ?_⟩⟩
  exact iff_of_true (hall h u hu t ht) (hall h u hu s hs)

end CFSG.OddTranspositions.PartFour
