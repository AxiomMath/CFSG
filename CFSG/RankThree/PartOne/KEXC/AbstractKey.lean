module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.RankThree.PartOne.KEXC

theorem twist_delta_fixed {M : Type*} [Group M] (φ : M → M) (adj : Subgroup M)
    (hmul : ∀ x ∈ adj, ∀ y ∈ adj, φ (x * y) = φ x * φ y)
    (hinv : ∀ x ∈ adj, φ x⁻¹ = (φ x)⁻¹) (Q : Subgroup M) (hQadj : Q ≤ adj)
    (hφQ : ∀ x ∈ Q, φ x ∈ Q) (P : Subgroup M) (hPQ : ∀ g ∈ P, g ∈ Q ∧ φ g = g)
    (hcent : ∀ y ∈ Q, (∀ g ∈ P, y * g = g * y) → y = 1) {e δ : M} (hδQ : δ ∈ Q)
    (hconj : ∀ x ∈ Q, e * x * e⁻¹ = δ * x * δ⁻¹)
    (hconjP : ∀ g ∈ P, e * g * e⁻¹ ∈ P) : φ δ = δ := by
  have hδadj : δ ∈ adj := hQadj hδQ
  have hy : δ⁻¹ * φ δ ∈ Q := mul_mem (inv_mem hδQ) (hφQ δ hδQ)
  have h1 : δ⁻¹ * φ δ = 1 := by
    refine hcent _ hy fun g hg => ?_
    obtain ⟨hgQ, hgφ⟩ := hPQ g hg
    have hgadj : g ∈ adj := hQadj hgQ
    have hegP := hconjP g hg
    have hφeg : φ (e * g * e⁻¹) = e * g * e⁻¹ := (hPQ _ hegP).2
    have h2 : φ (δ * g * δ⁻¹) = δ * g * δ⁻¹ := by rw [← hconj g hgQ]; exact hφeg
    rw [hmul _ (mul_mem hδadj hgadj) _ (inv_mem hδadj), hmul _ hδadj _ hgadj, hinv _ hδadj,
      hgφ] at h2
    calc δ⁻¹ * φ δ * g = δ⁻¹ * (φ δ * g * (φ δ)⁻¹) * φ δ := by group
      _ = δ⁻¹ * (δ * g * δ⁻¹) * φ δ := by rw [h2]
      _ = g * (δ⁻¹ * φ δ) := by group
  exact (inv_mul_eq_one.1 h1).symm

theorem bt_of_param {G H : Type*} [Group G] [Group H] (Λ : H →* G) (hΛ : Function.Injective Λ)
    {P : Subgroup G} (hP : ∀ g, g ∈ P ↔ ∃ s, g = Λ s) {R : Subgroup G} (hR0 : R ≠ ⊥)
    (hR2 : IsPGroup 2 R) (hRP : R ≤ P) {p : ℕ}
    (hBT : ∀ R₁ : Subgroup H, R₁ ≠ ⊥ → IsPGroup 2 R₁ → ∀ s : H, s ^ p = 1 →
      s ∈ Subgroup.normalizer (R₁ : Set H) → s = 1)
    {δ : G} (hδP : δ ∈ P) (hδp : δ ^ p = 1)
    (hnorm : ∀ x ∈ P, (x ∈ R ↔ δ * x * δ⁻¹ ∈ R)) : δ = 1 := by
  obtain ⟨s₀, hs₀⟩ := (hP δ).1 hδP
  let R₁ : Subgroup H := R.comap Λ
  have hR₁mem : ∀ s, s ∈ R₁ ↔ Λ s ∈ R := fun _ => Iff.rfl
  have hR₁ne : R₁ ≠ ⊥ := by
    obtain ⟨r, hr1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hR0
    obtain ⟨s, hs⟩ := (hP r).1 (hRP r.2)
    intro hbot
    have hmem : s ∈ R₁ := by
      rw [hR₁mem, ← hs]
      exact r.2
    rw [hbot, Subgroup.mem_bot] at hmem
    apply hr1
    exact Subtype.ext (by rw [hs, hmem, map_one]; rfl)
  have hR₁2 : IsPGroup 2 R₁ := hR2.comap_of_injective Λ hΛ
  have hs₀p : s₀ ^ p = 1 := by
    apply hΛ
    rw [map_pow, ← hs₀, hδp, map_one]
  have hs₀N : s₀ ∈ Subgroup.normalizer (R₁ : Set H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    rw [hR₁mem, hR₁mem, map_mul, map_mul, map_inv, ← hs₀]
    exact hnorm (Λ s) ((hP _).2 ⟨s, rfl⟩)
  have := hBT R₁ hR₁ne hR₁2 s₀ hs₀p hs₀N
  rw [hs₀, this, map_one]

end CFSG.RankThree.PartOne.KEXC
