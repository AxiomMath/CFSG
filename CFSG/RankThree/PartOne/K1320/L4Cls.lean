module

public import CFSG.RankThree.PartOne.K1320.L4Weyl

public section

namespace CFSG.RankThree.PartOne.K1320

open CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec1322Fin CFSG.RankThree.PartOne.Sec1322

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option maxRecDepth 100000

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem gp_classes1 : ∀ a : Gp, (isT a ∨ isV' a) → ∀ b : Gp, (isT b ∨ isV' b) → (a * b) ^ 4 = 1 →
    (a * b) ^ 2 ≠ 1 → ∀ x : Gp, (isT x ∨ isV' x) →
    (∃ g : Gp, g * a * g⁻¹ = x) ∨ (∃ g : Gp, g * b * g⁻¹ = x) := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem gp_classes2 : ∀ a : Gp, (isT' a ∨ isV' a) → ∀ b : Gp, (isT' b ∨ isV' b) → (a * b) ^ 4 = 1 →
    (a * b) ^ 2 ≠ 1 → ∀ x : Gp, (isT' x ∨ isV' x) →
    (∃ g : Gp, g * a * g⁻¹ = x) ∨ (∃ g : Gp, g * b * g⁻¹ = x) := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem gp_vclass1 : ∀ a : Gp, (isT a ∨ isV' a) → ∀ b : Gp, (isT b ∨ isV' b) → (a * b) ^ 4 = 1 →
    (a * b) ^ 2 ≠ 1 → ∀ s : Gp, (isT s ∨ isV' s) → a * s = s * a → b * s = s * b → s ≠ a →
    s ≠ b → s ≠ a * b * a⁻¹ → s ≠ b * a * b⁻¹ → (∃ g : Gp, g * b * g⁻¹ = s) →
    ∀ g : Gp, g * b * g⁻¹ = b ∨ g * b * g⁻¹ = a * b * a⁻¹ ∨ g * b * g⁻¹ = s := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
theorem gp_vclass2 : ∀ a : Gp, (isT' a ∨ isV' a) → ∀ b : Gp, (isT' b ∨ isV' b) → (a * b) ^ 4 = 1 →
    (a * b) ^ 2 ≠ 1 → ∀ s : Gp, (isT' s ∨ isV' s) → a * s = s * a → b * s = s * b → s ≠ a →
    s ≠ b → s ≠ a * b * a⁻¹ → s ≠ b * a * b⁻¹ → (∃ g : Gp, g * b * g⁻¹ = s) →
    ∀ g : Gp, g * b * g⁻¹ = b ∨ g * b * g⁻¹ = a * b * a⁻¹ ∨ g * b * g⁻¹ = s := by
  decide +kernel

variable {G : Type} [Group G] [Finite G]

namespace Bridge

variable {p : ℕ} {E : Subgroup G} (B : Bridge p E)

include B

theorem classes {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec12Hyp G p A c L E)
    (hcard : Nat.card E = p ^ 3) {a b : MulAut E} (ha : a ∈ reflectionSet p E)
    (hb : b ∈ reflectionSet p E) (hab : orderOf (a * b) = 4) {x : MulAut E}
    (hx : x ∈ reflectionSet p E) :
    (∃ g ∈ reflectionGroup p E, g * a * g⁻¹ = x) ∨
      (∃ g ∈ reflectionGroup p E, g * b * g⁻¹ = x) := by
  obtain ⟨a', rfl, -, -, -⟩ := B.refl_data h hcard ha
  obtain ⟨b', rfl, -, -, -⟩ := B.refl_data h hcard hb
  obtain ⟨x', rfl, -, -, -⟩ := B.refl_data h hcard hx
  have hinv : ∀ g : Gp, B.φ g⁻¹ = (B.φ g)⁻¹ := fun g =>
    eq_inv_of_mul_eq_one_right (by rw [← map_mul, mul_inv_cancel, map_one])
  have ho : orderOf (a' * b') = 4 := by
    rw [← orderOf_injective B.φ B.inj, map_mul]; exact hab
  have h4 : (a' * b') ^ 4 = 1 := by
    have := pow_orderOf_eq_one (a' * b')
    rwa [ho] at this
  have h2 : (a' * b') ^ 2 ≠ 1 := by
    intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [ho] at this
    omega
  have key : (∃ g : Gp, g * a' * g⁻¹ = x') ∨ (∃ g : Gp, g * b' * g⁻¹ = x') := by
    rcases B.shape with hshape | hshape
    · exact gp_classes1 a' ((hshape a').1 ha) b' ((hshape b').1 hb) h4 h2 x' ((hshape x').1 hx)
    · exact gp_classes2 a' ((hshape a').1 ha) b' ((hshape b').1 hb) h4 h2 x' ((hshape x').1 hx)
  rcases key with ⟨g, hg⟩ | ⟨g, hg⟩
  · left
    refine ⟨B.φ g, B.mem g, ?_⟩
    rw [← hinv, ← map_mul, ← map_mul, hg]
  · right
    refine ⟨B.φ g, B.mem g, ?_⟩
    rw [← hinv, ← map_mul, ← map_mul, hg]

theorem vclass {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec12Hyp G p A c L E)
    (hcard : Nat.card E = p ^ 3) {a b s : MulAut E} (ha : a ∈ reflectionSet p E)
    (hb : b ∈ reflectionSet p E) (hs : s ∈ reflectionSet p E) (hab : orderOf (a * b) = 4)
    (cas : a * s = s * a) (cbs : b * s = s * b) (hsa : s ≠ a) (hsb : s ≠ b)
    (hsaba : s ≠ a * b * a⁻¹) (hsbab : s ≠ b * a * b⁻¹)
    (hsconj : ∃ g ∈ reflectionGroup p E, g * b * g⁻¹ = s) :
    ∀ g ∈ reflectionGroup p E, g * b * g⁻¹ = b ∨ g * b * g⁻¹ = a * b * a⁻¹ ∨
      g * b * g⁻¹ = s := by
  obtain ⟨a', rfl, -, -, -⟩ := B.refl_data h hcard ha
  obtain ⟨b', rfl, -, -, -⟩ := B.refl_data h hcard hb
  obtain ⟨s', rfl, -, -, -⟩ := B.refl_data h hcard hs
  have hinv : ∀ g : Gp, B.φ g⁻¹ = (B.φ g)⁻¹ := fun g =>
    eq_inv_of_mul_eq_one_right (by rw [← map_mul, mul_inv_cancel, map_one])
  have ho : orderOf (a' * b') = 4 := by
    rw [← orderOf_injective B.φ B.inj, map_mul]; exact hab
  have h4 : (a' * b') ^ 4 = 1 := by
    have := pow_orderOf_eq_one (a' * b')
    rwa [ho] at this
  have h2 : (a' * b') ^ 2 ≠ 1 := by
    intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [ho] at this
    omega
  have c1 : a' * s' = s' * a' := B.inj (by rw [map_mul, map_mul]; exact cas)
  have c2 : b' * s' = s' * b' := B.inj (by rw [map_mul, map_mul]; exact cbs)
  have n1 : s' ≠ a' := fun h1 => hsa (by rw [h1])
  have n2 : s' ≠ b' := fun h1 => hsb (by rw [h1])
  have n3 : s' ≠ a' * b' * a'⁻¹ := fun h1 => hsaba (by rw [h1, map_mul, map_mul, hinv])
  have n4 : s' ≠ b' * a' * b'⁻¹ := fun h1 => hsbab (by rw [h1, map_mul, map_mul, hinv])
  have hconj' : ∃ g : Gp, g * b' * g⁻¹ = s' := by
    obtain ⟨g, hg, hgs⟩ := hsconj
    obtain ⟨g', rfl⟩ := B.surj g hg
    exact ⟨g', B.inj (by rw [map_mul, map_mul, hinv]; exact hgs)⟩
  intro g hg
  obtain ⟨g', rfl⟩ := B.surj g hg
  have key : g' * b' * g'⁻¹ = b' ∨ g' * b' * g'⁻¹ = a' * b' * a'⁻¹ ∨ g' * b' * g'⁻¹ = s' := by
    rcases B.shape with hshape | hshape
    · exact gp_vclass1 a' ((hshape a').1 ha) b' ((hshape b').1 hb) h4 h2 s' ((hshape s').1 hs)
        c1 c2 n1 n2 n3 n4 hconj' g'
    · exact gp_vclass2 a' ((hshape a').1 ha) b' ((hshape b').1 hb) h4 h2 s' ((hshape s').1 hs)
        c1 c2 n1 n2 n3 n4 hconj' g'
  rcases key with k | k | k
  · left
    rw [← hinv, ← map_mul, ← map_mul, k]
  · right; left
    rw [← hinv, ← map_mul, ← map_mul, k, map_mul, map_mul, hinv]
  · right; right
    rw [← hinv, ← map_mul, ← map_mul, k]

end Bridge

end CFSG.RankThree.PartOne.K1320
