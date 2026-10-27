module

public import Mathlib.Algebra.Group.Subgroup.Lattice

public section

theorem Subgroup.mem_sup_iff_of_forall_commute {G : Type*} [Group G] {H K : Subgroup G}
    (h : ∀ x ∈ H, ∀ y ∈ K, x * y = y * x) {z : G} :
    z ∈ H ⊔ K ↔ ∃ x ∈ H, ∃ y ∈ K, z = x * y := by
  constructor
  · intro hz
    let T : Subgroup G :=
      { carrier := {z | ∃ x ∈ H, ∃ y ∈ K, z = x * y}
        one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
        mul_mem' := by
          rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
          refine ⟨a * a', H.mul_mem ha ha', b * b', K.mul_mem hb hb', ?_⟩
          calc (a * b) * (a' * b')
              = a * (b * (a' * b')) := mul_assoc a b (a' * b')
            _ = a * ((b * a') * b') := by rw [← mul_assoc b a' b']
            _ = a * ((a' * b) * b') := by rw [← h a' ha' b hb]
            _ = a * (a' * (b * b')) := by rw [mul_assoc a' b b']
            _ = (a * a') * (b * b') := by rw [← mul_assoc a a' (b * b')]
        inv_mem' := by
          rintro _ ⟨a, ha, b, hb, rfl⟩
          exact ⟨a⁻¹, H.inv_mem ha, b⁻¹, K.inv_mem hb,
            by rw [mul_inv_rev, h a⁻¹ (H.inv_mem ha) b⁻¹ (K.inv_mem hb)]⟩ }
    have hle : H ⊔ K ≤ T := sup_le (fun a ha => ⟨a, ha, 1, K.one_mem, by simp⟩)
      (fun b hb => ⟨1, H.one_mem, b, hb, by simp⟩)
    exact hle hz
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact Subgroup.mul_mem_sup hx hy
