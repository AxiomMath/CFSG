module

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Algebra.Group.Subgroup.Defs

public section

namespace CFSG.Quasithin

theorem exists_ext {G : Type*} [Group G] {E F : Subgroup G} [Finite E] (hFE : F ≤ E)
    (hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hsq : ∀ a ∈ E, a * a = 1)
    {g : G} (hg : g ∈ E) (hgF : g ∉ F) :
    ∃ F' : Subgroup G, F ≤ F' ∧ g ∈ F' ∧ F' ≤ E ∧ Nat.card F' = 2 * Nat.card F := by
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right (hsq g hg)
  have hgy : ∀ y ∈ F, g * y = y * g := fun y hy => hcomm g hg y (hFE hy)
  let F' : Subgroup G :=
    { carrier := {x | x ∈ F ∨ ∃ y ∈ F, x = g * y}
      one_mem' := Or.inl F.one_mem
      mul_mem' := by
        rintro a b (ha | ⟨y, hy, rfl⟩) (hb | ⟨z, hz, rfl⟩)
        · exact Or.inl (F.mul_mem ha hb)
        · refine Or.inr ⟨a * z, F.mul_mem ha hz, ?_⟩
          rw [← mul_assoc, hcomm a (hFE ha) g hg, mul_assoc]
        · exact Or.inr ⟨y * b, F.mul_mem hy hb, by rw [mul_assoc]⟩
        · refine Or.inl ?_
          have : g * y * (g * z) = y * z := by
            rw [mul_assoc, ← mul_assoc y g z, ← hgy y hy, ← mul_assoc, ← mul_assoc, hsq g hg,
              one_mul]
          rw [this]
          exact F.mul_mem hy hz
      inv_mem' := by
        rintro a (ha | ⟨y, hy, rfl⟩)
        · exact Or.inl (F.inv_mem ha)
        · refine Or.inr ⟨y⁻¹, F.inv_mem hy, ?_⟩
          rw [mul_inv_rev, hginv, ← hgy y⁻¹ (F.inv_mem hy)] }
  have hmem : ∀ x, x ∈ F' ↔ x ∈ F ∨ ∃ y ∈ F, x = g * y := fun x => Iff.rfl
  have hFF' : F ≤ F' := fun x hx => Or.inl hx
  have hgF' : g ∈ F' := Or.inr ⟨1, F.one_mem, (mul_one g).symm⟩
  have hF'E : F' ≤ E := by
    rintro x (hx | ⟨y, hy, rfl⟩)
    · exact hFE hx
    · exact E.mul_mem hg (hFE hy)
  refine ⟨F', hFF', hgF', hF'E, ?_⟩
  have : Finite F := Finite.of_injective (Subgroup.inclusion hFE) (Subgroup.inclusion_injective hFE)
  let φ : F ⊕ F → F' := Sum.elim (fun y => ⟨y.1, Or.inl y.2⟩) (fun y => ⟨g * y.1, Or.inr ⟨y.1, y.2, rfl⟩⟩)
  have hφ : Function.Bijective φ := by
    constructor
    · rintro (⟨y, hy⟩ | ⟨y, hy⟩) (⟨z, hz⟩ | ⟨z, hz⟩) h
      · have := congrArg Subtype.val h
        simp only [φ, Sum.elim_inl] at this
        subst this
        rfl
      · exfalso
        have h' := congrArg Subtype.val h
        simp only [φ, Sum.elim_inl, Sum.elim_inr] at h'
        apply hgF
        have : g = y * z⁻¹ := by rw [h']; simp
        rw [this]
        exact F.mul_mem hy (F.inv_mem hz)
      · exfalso
        have h' := congrArg Subtype.val h
        simp only [φ, Sum.elim_inl, Sum.elim_inr] at h'
        apply hgF
        have : g = z * y⁻¹ := by rw [← h']; simp
        rw [this]
        exact F.mul_mem hz (F.inv_mem hy)
      · have := congrArg Subtype.val h
        simp only [φ, Sum.elim_inr] at this
        have := mul_left_cancel this
        subst this
        rfl
    · rintro ⟨x, hx | ⟨y, hy, rfl⟩⟩
      · exact ⟨Sum.inl ⟨x, hx⟩, rfl⟩
      · exact ⟨Sum.inr ⟨y, hy⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_sum]
  omega

end CFSG.Quasithin
