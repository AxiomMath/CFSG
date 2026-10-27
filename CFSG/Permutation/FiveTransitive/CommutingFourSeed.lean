module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

namespace FiveTransitive.CommutingFourSeed

open MulAction

@[expose] def Seed (G X : Type*) [Group G] [MulAction G X] : Prop :=
  ∀ (s : Set X), s.ncard = 4 → ∀ K : Subgroup G, IsPGroup 2 K →
    (∀ k : G, k ∈ K → ∀ x ∈ s, k • x ∈ s) →
    ∃ b : G, b * b = 1 ∧ b ≠ 1 ∧ (∀ x ∈ s, b • x = x) ∧
      ∀ k : G, k ∈ K → k * b = b * k

theorem exists_pair_group
    {G : Type*} [Group G] (a b : G) (ha : a * a = 1) (hb : b * b = 1)
    (hab : a * b = b * a) :
    ∃ K : Subgroup G, IsPGroup 2 K ∧
      ∀ g : G, g ∈ K ↔ g = 1 ∨ g = a ∨ g = b ∨ g = a * b := by
  have haa (g : G) : a * (a * g) = g := by rw [← mul_assoc, ha, one_mul]
  have habb : a * b * b = a := by rw [mul_assoc, hb, mul_one]
  have haba : a * b * a = b := by rw [hab, mul_assoc, ha, mul_one]
  have hb_ab : b * (a * b) = a := by rw [← mul_assoc, ← hab, habb]
  have habab : (a * b) * (a * b) = 1 := by rw [← mul_assoc, haba, hb]
  have hiA : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hiB : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  let K : Subgroup G :=
    { carrier := {g | g = 1 ∨ g = a ∨ g = b ∨ g = a * b}
      one_mem' := Or.inl rfl
      mul_mem' := by
        intro x y hx hy
        rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
          simp only [Set.mem_ofPred_eq, one_mul, mul_one, ha, hb, haa, hb_ab, habb, haba,
            habab, ← hab, or_true, true_or, eq_self]
      inv_mem' := by
        intro x hx
        rcases hx with rfl | rfl | rfl | rfl <;>
          simp only [Set.mem_ofPred_eq, inv_one, hiA, hiB, mul_inv_rev, ← hab,
            or_true, true_or, eq_self] }
  have hsq (k : K) : k * k = 1 := by
    apply Subtype.ext
    change k.val * k.val = 1
    rcases k.property with h | h | h | h
    · rw [h, one_mul]
    · rw [h, ha]
    · rw [h, hb]
    · rw [h, habab]
  refine ⟨K, ?_, fun _ => Iff.rfl⟩
  apply isPGroup_iff_orderOf_dvd_pow.mpr
  intro k
  refine ⟨1, ?_⟩
  rw [pow_one]
  exact orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq k)

theorem for_pair
    {G X : Type*} [Group G] [MulAction G X] (hseed : Seed G X)
    (s : Set X) (hs : s.ncard = 4) (a b : G)
    (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    (has : ∀ x ∈ s, a • x ∈ s) (hbs : ∀ x ∈ s, b • x ∈ s) :
    ∃ c : G, c * c = 1 ∧ c ≠ 1 ∧ (∀ x ∈ s, c • x = x) ∧
      a * c = c * a ∧ b * c = c * b := by
  obtain ⟨K, hK, hmem⟩ := exists_pair_group a b ha hb hab
  obtain ⟨c, hc, hc1, hfix, hcomm⟩ := hseed s hs K hK (by
    intro k hk x hx
    rcases (hmem k).mp hk with rfl | rfl | rfl | rfl
    · simpa only [one_smul] using hx
    · exact has x hx
    · exact hbs x hx
    · rw [mul_smul]; exact has _ (hbs x hx))
  exact ⟨c, hc, hc1, hfix, hcomm a ((hmem a).mpr (Or.inr (Or.inl rfl))),
    hcomm b ((hmem b).mpr (Or.inr (Or.inr (Or.inl rfl))))⟩

theorem for_one
    {G X : Type*} [Group G] [MulAction G X] (hseed : Seed G X)
    (s : Set X) (hs : s.ncard = 4) (a : G) (ha : a * a = 1)
    (has : ∀ x ∈ s, a • x ∈ s) :
    ∃ b : G, b * b = 1 ∧ b ≠ 1 ∧ (∀ x ∈ s, b • x = x) ∧ a * b = b * a := by
  obtain ⟨b, hb, hb1, hfix, hab, _⟩ := for_pair hseed s hs a 1 ha (one_mul 1)
    (by simp only [mul_one, one_mul]) has (by intro x hx; simpa only [one_smul] using hx)
  exact ⟨b, hb, hb1, hfix, hab⟩

end FiveTransitive.CommutingFourSeed

end CFSG
