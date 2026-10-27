module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDNbrFixAlg

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private def plnf_chi {m : ℕ} (ε : Bool) (c d i : Fin m) : ZMod 3 :=
  if i = c ∨ i = d then (if ε then (-1 : ZMod 3) else 1) else 1

private lemma plnf_dTau_coord (m : ℕ) (ε : Bool) {c d : Fin m} (hcd : c ≠ d) (u : DVec m)
    (i : Fin m) : dTau m ε c d u i = plnf_chi ε c d i * u (Equiv.swap c d i) := by
  unfold plnf_chi
  by_cases hic : i = c
  · rw [hic, dTau_coord_left m ε hcd, Equiv.swap_apply_left]
    simp
  · by_cases hid : i = d
    · rw [hid, dTau_coord_right m ε hcd, Equiv.swap_apply_right]
      simp
    · rw [dTau_coord_of_ne m ε hcd hic hid, Equiv.swap_apply_of_ne_of_ne hic hid]
      simp [hic, hid]

private lemma plnf_chi_swap {m : ℕ} (ε : Bool) {c d : Fin m} (x : Fin m) :
    plnf_chi ε c d (Equiv.swap c d x) = plnf_chi ε c d x := by
  unfold plnf_chi
  by_cases hxc : x = c
  · rw [hxc, Equiv.swap_apply_left]
    simp
  · by_cases hxd : x = d
    · rw [hxd, Equiv.swap_apply_right]
      simp
    · rw [Equiv.swap_apply_of_ne_of_ne hxc hxd]

private lemma plnf_chi_sign {m : ℕ} (ε : Bool) (c d i : Fin m) :
    plnf_chi ε c d i = 1 ∨ plnf_chi ε c d i = -1 := by
  unfold plnf_chi
  by_cases h : i = c ∨ i = d
  · rw [if_pos h]
    cases ε <;> simp
  · rw [if_neg h]
    exact Or.inl rfl

private lemma plnf_chi_sq {m : ℕ} (ε : Bool) (c d i : Fin m) :
    plnf_chi ε c d i * plnf_chi ε c d i = 1 := by
  rcases plnf_chi_sign ε c d i with h | h <;> rw [h] <;> decide

private lemma plnf_sign_mul {x y : ZMod 3} (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) :
    x * y = 1 ∨ x * y = -1 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> decide

private lemma plnf_exists_sign {x : ZMod 3} (hx : x = 1 ∨ x = -1) :
    ∃ ε : Bool, (if ε then (-1 : ZMod 3) else 1) = x := by
  rcases hx with rfl | rfl
  · exact ⟨false, rfl⟩
  · exact ⟨true, rfl⟩

theorem dTau_conj_dTau (m : ℕ) (ε ε' : Bool) {a b c d : Fin m} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ (ε'' : Bool) (a' b' : Fin m), a' ≠ b' ∧
      dTau m ε c d * dTau m ε' a b * (dTau m ε c d)⁻¹ = dTau m ε'' a' b' := by
  have hτsign : (if ε' then (-1 : ZMod 3) else 1) = 1 ∨ (if ε' then (-1 : ZMod 3) else 1) = -1 := by
    cases ε' <;> simp
  obtain ⟨ε'', hε''⟩ := plnf_exists_sign (plnf_sign_mul (plnf_sign_mul
    (plnf_chi_sign ε c d a) (plnf_chi_sign ε c d b)) hτsign)
  have hab' : Equiv.swap c d a ≠ Equiv.swap c d b := fun h => hab ((Equiv.swap c d).injective h)
  refine ⟨ε'', Equiv.swap c d a, Equiv.swap c d b, hab', ?_⟩
  rw [dTau_inv m ε hcd]
  refine LinearEquiv.ext fun v => funext fun i => ?_
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, plnf_dTau_coord m ε hcd]
  by_cases h1 : i = Equiv.swap c d a
  · rw [h1, Equiv.swap_apply_self, dTau_coord_left m ε' hab, plnf_dTau_coord m ε hcd v b,
      dTau_coord_left m ε'' hab', hε'', plnf_chi_swap]
    ring
  · by_cases h2 : i = Equiv.swap c d b
    · rw [h2, Equiv.swap_apply_self, dTau_coord_right m ε' hab, plnf_dTau_coord m ε hcd v a,
        dTau_coord_right m ε'' hab', hε'', plnf_chi_swap]
      ring
    · have h1' : Equiv.swap c d i ≠ a := fun h => h1 (Equiv.swap_apply_eq_iff.mp h)
      have h2' : Equiv.swap c d i ≠ b := fun h => h2 (Equiv.swap_apply_eq_iff.mp h)
      rw [dTau_coord_of_ne m ε' hab h1' h2', dTau_coord_of_ne m ε'' hab' h1 h2,
        plnf_dTau_coord m ε hcd v (Equiv.swap c d i), Equiv.swap_apply_self, plnf_chi_swap,
        ← mul_assoc, plnf_chi_sq, one_mul]

theorem dTau_conj_mem_closure (m : ℕ) {u : DVec m ≃ₗ[ZMod 3] DVec m}
    (hu : u ∈ Subgroup.closure
      {x : DVec m ≃ₗ[ZMod 3] DVec m | ∃ (ε : Bool) (a b : Fin m), a ≠ b ∧ x = dTau m ε a b})
    (ε : Bool) {a b : Fin m} (hab : a ≠ b) :
    ∃ (ε' : Bool) (a' b' : Fin m), a' ≠ b' ∧ u * dTau m ε a b * u⁻¹ = dTau m ε' a' b' := by
  have hsub : {x : DVec m ≃ₗ[ZMod 3] DVec m |
      ∃ (ε : Bool) (a b : Fin m), a ≠ b ∧ x = dTau m ε a b} ⊆
      (Subgroup.normalizer {x : DVec m ≃ₗ[ZMod 3] DVec m |
        ∃ (ε : Bool) (a b : Fin m), a ≠ b ∧ x = dTau m ε a b} : Set _) := by
    rintro g ⟨ε₀, c, d, hcd, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_set_normalizer_iff]
    intro x
    constructor
    · rintro ⟨ε₁, a, b, hab, rfl⟩
      obtain ⟨ε'', a', b', h', h⟩ := dTau_conj_dTau m ε₀ ε₁ hab hcd
      exact ⟨ε'', a', b', h', h⟩
    · rintro ⟨ε₁, a, b, hab, h⟩
      obtain ⟨ε'', a', b', h', h''⟩ := dTau_conj_dTau m ε₀ ε₁ hab hcd
      refine ⟨ε'', a', b', h', ?_⟩
      calc x = (dTau m ε₀ c d)⁻¹ * (dTau m ε₀ c d * x * (dTau m ε₀ c d)⁻¹) * dTau m ε₀ c d := by
            group
        _ = (dTau m ε₀ c d)⁻¹ * dTau m ε₁ a b * dTau m ε₀ c d := by rw [h]
        _ = dTau m ε₀ c d * dTau m ε₁ a b * (dTau m ε₀ c d)⁻¹ := by rw [dTau_inv m ε₀ hcd]
        _ = dTau m ε'' a' b' := h''
  have hmem := Subgroup.closure_le _ |>.mpr hsub hu
  rw [Subgroup.mem_set_normalizer_iff] at hmem
  exact (hmem (dTau m ε a b)).mp ⟨ε, a, b, hab, rfl⟩

end CFSG.StandardType.QTwo

end
