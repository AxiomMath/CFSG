module

public import CFSG.Sporadic.Co2Smith.GlDataC0Card

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.Co2Rank3 MulAction

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem glPt_spec :
    (∀ k < 11, Native.glMaps Native.glRows[k]! 80 80 = true) ∧
    mulRows 22 Native.glU Native.glU = idRows 22 ∧ Native.glMaps Native.glU 80 1172 = true ∧
    Native.glMaps Native.glV 80 1348 = true ∧ Native.glMaps Native.glV1 80 582 = true ∧
    mulRows 22 Native.glV1 Native.glV1 = idRows 22 := by
  have h := glElem_parts.2.2.1
  simp only [Native.glPtOK, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem co2PermHom_uK :
    co2PermHom uK glP0 = 1172 :=
  co2PermHom_apply_of_maps uK_val (by norm_num) (by norm_num) glPt_spec.2.2.1

theorem co2PermHom_v1K :
    co2PermHom v1K glP0 = 582 :=
  co2PermHom_apply_of_maps v1K_val (by norm_num) (by norm_num) glPt_spec.2.2.2.2.1

theorem uK_mul_self :
    uK * uK = 1 := by
  apply eq_of_val_eq
  rw [val_val_mul, uK_val, ← rowsMatrix_mulRows, glPt_spec.2.1, rowsMatrix_idRows]
  rfl

theorem v1K_mul_self :
    v1K * v1K = 1 := by
  apply eq_of_val_eq
  rw [val_val_mul, v1K_val, ← rowsMatrix_mulRows, glPt_spec.2.2.2.2.2, rowsMatrix_idRows]
  rfl

theorem glFormK_one : glFormK 1 = uK := by
  simp [glFormK]

theorem glFormK_two : glFormK 2 = vK := by
  simp [glFormK]

theorem mem_glWit0Pts {t x : ℕ} :
    x ∈ Native.glWit0Pts t ↔ ∃ e ∈ Native.glWit0, e.2.1 = t ∧ e.1 = x := by
  simp only [Native.glWit0Pts, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨e, ⟨he, ht⟩, rfl⟩
    exact ⟨e, he, ht, rfl⟩
  · rintro ⟨e, he, ht, rfl⟩
    exact ⟨e, ⟨he, ht⟩, rfl⟩

theorem mem_C0c_iff
    {g : K} :
    g ∈ C0c ↔ g ∈ C1c ∨ (∃ a ∈ C1c, ∃ b ∈ C1c, g = a * uK * b) ∨
      ∃ a ∈ C1c, ∃ b ∈ C1c, g = a * vK * b := by
  constructor
  · intro hg
    have hy : co2PermHom g glP0 ∈ orbit (stabChain (G := C0P) glBasePt 0) (glBasePt 0) := by
      rw [← orbit_C0P_eq]
      exact ⟨⟨co2PermHom g, g, hg, rfl⟩, rfl⟩
    rw [orbit_C0P_zero] at hy
    obtain ⟨e, he, hex⟩ := List.mem_map.1 hy
    obtain ⟨hx, hC0, hfix, ht, hmap⟩ := glWit0_spec he
    have hb : (glE e.2.2 * glFormK e.2.1)⁻¹ * g ∈ C1c := by
      refine ⟨C0c.mul_mem (C0c.inv_mem (C0c.mul_mem hC0 (glFormK_mem_C0c _))) hg, ?_⟩
      show co2PermHom ((glE e.2.2 * glFormK e.2.1)⁻¹ * g) glP0 = glP0
      have h1 : co2PermHom g glP0 = co2PermHom (glE e.2.2 * glFormK e.2.1) glP0 := by
        rw [hmap]
        exact Fin.ext hex.symm
      rw [map_mul, map_inv, Equiv.Perm.mul_apply, h1, perm_inv_apply_self]
    have ha : glE e.2.2 ∈ C1c := ⟨hC0, hfix⟩
    have hg' : g = glE e.2.2 * glFormK e.2.1 * ((glE e.2.2 * glFormK e.2.1)⁻¹ * g) := by
      group
    rcases (show e.2.1 = 0 ∨ e.2.1 = 1 ∨ e.2.1 = 2 by omega) with h | h | h <;>
      rw [h] at hg' hb
    · left
      rw [hg']
      exact C1c.mul_mem (C1c.mul_mem ha (by rw [glFormK_zero]; exact C1c.one_mem)) hb
    · exact Or.inr (Or.inl ⟨_, ha, _, hb, by rw [← glFormK_one]; exact hg'⟩)
    · exact Or.inr (Or.inr ⟨_, ha, _, hb, by rw [← glFormK_two]; exact hg'⟩)
  · rintro (hg | ⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, b, hb, rfl⟩)
    · exact hg.1
    · exact C0c.mul_mem (C0c.mul_mem ha.1 uK_mem_C0c) hb.1
    · exact C0c.mul_mem (C0c.mul_mem ha.1 vK_mem_C0c) hb.1

end CFSG.Sporadic.Co2Smith
