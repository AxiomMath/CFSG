module

public import CFSG.Quasithin.Recognition.M22Witt

public section

namespace CFSG.Quasithin.M22Witt

open MulAction CFSG.ComponentClassification.WittDesign CFSG.Quasithin.Asc94
open scoped Pointwise

theorem exists_double_coset_two
    {k j : M22} (hk : k ∈ stabilizer M22 (0 : Fin 22))
    (hk1 : k ∉ m22TwoStab) (hj : j ∈ stabilizer M22 (0 : Fin 22)) (hj1 : j ∉ m22TwoStab) :
    ∃ x ∈ m22TwoStab, ∃ y ∈ m22TwoStab, k = x * j * y := by
  have hk0 : k • (0 : Fin 22) = 0 := MulAction.mem_stabilizer_iff.mp hk
  have hj0 : j • (0 : Fin 22) = 0 := MulAction.mem_stabilizer_iff.mp hj
  have hk1' : k • (1 : Fin 22) ≠ 1 := fun h =>
    hk1 (Subgroup.mem_inf.mpr ⟨hk, MulAction.mem_stabilizer_iff.mpr h⟩)
  have hj1' : j • (1 : Fin 22) ≠ 1 := fun h =>
    hj1 (Subgroup.mem_inf.mpr ⟨hj, MulAction.mem_stabilizer_iff.mpr h⟩)
  have hk10 : k • (1 : Fin 22) ≠ 0 := by
    intro h
    rw [← hk0] at h
    exact absurd (smul_left_cancel _ h) (by decide)
  have hj10 : j • (1 : Fin 22) ≠ 0 := by
    intro h
    rw [← hj0] at h
    exact absurd (smul_left_cancel _ h) (by decide)
  obtain ⟨x, hx0, hx1, hxj⟩ := exists_smul_eq_triple (a := (0 : Fin 22)) (b := 1)
    (c := j • (1 : Fin 22)) (a' := 0) (b' := 1) (c' := k • (1 : Fin 22)) (by decide)
    (Ne.symm hj10) (Ne.symm hj1') (by decide) (Ne.symm hk10) (Ne.symm hk1')
  have hxS : x ∈ m22TwoStab := Subgroup.mem_inf.mpr
    ⟨MulAction.mem_stabilizer_iff.mpr hx0, MulAction.mem_stabilizer_iff.mpr hx1⟩
  refine ⟨x, hxS, j⁻¹ * x⁻¹ * k, Subgroup.mem_inf.mpr ⟨MulAction.mem_stabilizer_iff.mpr ?_,
    MulAction.mem_stabilizer_iff.mpr ?_⟩, by group⟩
  · have hx0' : x⁻¹ • (0 : Fin 22) = 0 := by rw [inv_smul_eq_iff, hx0]
    have hj0' : j⁻¹ • (0 : Fin 22) = 0 := by rw [inv_smul_eq_iff, hj0]
    rw [mul_smul, mul_smul, hk0, hx0', hj0']
  · rw [mul_smul, mul_smul, ← hxj, inv_smul_smul, inv_smul_smul]

section Local

variable {G : Type*} [Group G] {K : Subgroup G} (Φ : K ≃* stabilizer M22 (0 : Fin 22)) {t j : G}

theorem exists_eq_mul_mul
    (hj : j ∈ K) (hj₁ : (Φ ⟨j, hj⟩ : M22) ∉ m22TwoStab) (k : K)
    (hk : (Φ k : M22) ∉ m22TwoStab) :
    ∃ x : K, (Φ x : M22) ∈ m22TwoStab ∧ ∃ y : K, (Φ y : M22) ∈ m22TwoStab ∧
      (k : G) = x * j * y := by
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_double_coset_two (Φ k).2 hk (Φ ⟨j, hj⟩).2 hj₁
  have hx0 : x ∈ stabilizer M22 (0 : Fin 22) := (Subgroup.mem_inf.mp hx).1
  have hy0 : y ∈ stabilizer M22 (0 : Fin 22) := (Subgroup.mem_inf.mp hy).1
  refine ⟨Φ.symm ⟨x, hx0⟩, by rw [MulEquiv.apply_symm_apply]; exact hx, Φ.symm ⟨y, hy0⟩,
    by rw [MulEquiv.apply_symm_apply]; exact hy, ?_⟩
  have h1 : k = Φ.symm ⟨x, hx0⟩ * ⟨j, hj⟩ * Φ.symm ⟨y, hy0⟩ := by
    apply Φ.injective
    apply Subtype.ext
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
      Subgroup.coe_mul, Subgroup.coe_mul]
    exact hxy
  rw [h1, Subgroup.coe_mul, Subgroup.coe_mul]

theorem triangle_eq (htt : t * t = 1) (hjj : j * j = 1) (htj : (t * j) ^ 3 = 1) :
    t * j * t = j * t * j := by
  have h3 : t * j * t * (j * t * j) = 1 := by simpa only [pow_three, mul_assoc] using htj
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hjinv : j⁻¹ = j := inv_eq_of_mul_eq_one_right hjj
  rw [eq_inv_of_mul_eq_one_left h3, mul_inv_rev, mul_inv_rev, htinv, hjinv, mul_assoc]

theorem exists_subgroup_doubleCoset
    (htt : t * t = 1)
    (ht : ∀ k : K, t * (k : G) * t ∈ K ↔ (Φ k : M22) ∈ m22TwoStab)
    (hj : j ∈ K) (hj₁ : (Φ ⟨j, hj⟩ : M22) ∉ m22TwoStab) (hjj : j * j = 1)
    (htj : (t * j) ^ 3 = 1) :
    ∃ I : Subgroup G, ∀ g, g ∈ I ↔ g ∈ K ∨ ∃ a ∈ K, ∃ b ∈ K, g = a * t * b := by
  set S : Set G := {g | g ∈ K ∨ ∃ a ∈ K, ∃ b ∈ K, g = a * t * b} with hS
  have hleft : ∀ {a g : G}, a ∈ K → g ∈ S → a * g ∈ S := by
    rintro a g ha (hg | ⟨c, hc, d, hd, rfl⟩)
    · exact Or.inl (K.mul_mem ha hg)
    · exact Or.inr ⟨a * c, K.mul_mem ha hc, d, hd, by group⟩
  have hright : ∀ {g b : G}, g ∈ S → b ∈ K → g * b ∈ S := by
    rintro g b (hg | ⟨c, hc, d, hd, rfl⟩) hb
    · exact Or.inl (K.mul_mem hg hb)
    · exact Or.inr ⟨c, hc, d * b, K.mul_mem hd hb, by group⟩
  have htri := triangle_eq htt hjj htj
  have hkey : ∀ k ∈ K, t * k * t ∈ S := by
    intro k hk
    by_cases h : (Φ ⟨k, hk⟩ : M22) ∈ m22TwoStab
    · exact Or.inl ((ht ⟨k, hk⟩).mpr h)
    · obtain ⟨x, hx, y, hy, hxy⟩ := exists_eq_mul_mul Φ hj hj₁ ⟨k, hk⟩ h
      have hxt := (ht x).mpr hx
      have hyt := (ht y).mpr hy
      refine Or.inr ⟨t * x * t * j, K.mul_mem hxt hj, j * (t * y * t), K.mul_mem hj hyt, ?_⟩
      have e1 : t * (x * j * y : G) * t = t * x * t * (t * j * t) * (t * y * t) := by
        calc t * (x * j * y : G) * t = t * x * (t * t) * j * (t * t) * y * t := by
              rw [htt]; group
          _ = t * x * t * (t * j * t) * (t * y * t) := by group
      simp only at hxy
      rw [hxy, e1, htri]
      group
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  refine ⟨{ carrier := S, mul_mem' := ?_, one_mem' := Or.inl K.one_mem, inv_mem' := ?_ },
    fun g => Iff.rfl⟩
  · rintro g₁ g₂ hg₁ (hg₂ | ⟨c, hc, d, hd, rfl⟩)
    · exact hright hg₁ hg₂
    · rcases hg₁ with hg₁ | ⟨a, ha, b, hb, rfl⟩
      · exact Or.inr ⟨g₁ * c, K.mul_mem hg₁ hc, d, hd, by group⟩
      · have e : a * t * b * (c * t * d) = a * (t * (b * c) * t) * d := by group
        rw [e]
        exact hright (hleft ha (hkey _ (K.mul_mem hb hc))) hd
  · rintro g (hg | ⟨a, ha, b, hb, rfl⟩)
    · exact Or.inl (K.inv_mem hg)
    · refine Or.inr ⟨b⁻¹, K.inv_mem hb, a⁻¹, K.inv_mem ha, ?_⟩
      rw [mul_inv_rev, mul_inv_rev, htinv, mul_assoc]

end Local

theorem nonempty_mulEquiv_m22_of_local
    {G : Type*} [Group G] [Finite G] {K H : Subgroup G}
    (Φ : K ≃* stabilizer M22 (0 : Fin 22)) (hgen : K ⊔ H = ⊤)
    (hH : ∀ k : K, (k : G) ∈ H ↔ (Φ k : M22) ∈ m22PtHexStab) (hH6 : K.relIndex H = 6)
    {t j : G} (htt : t * t = 1)
    (ht : ∀ k : K, t * (k : G) * t ∈ K ↔ (Φ k : M22) ∈ m22TwoStab)
    (hHt : ∀ h ∈ H, h ∈ K ∨ ∃ a ∈ H ⊓ K, ∃ b ∈ H ⊓ K, h = a * t * b)
    (hj : j ∈ K) (hj₁ : (Φ ⟨j, hj⟩ : M22) ∉ m22TwoStab) (hjj : j * j = 1)
    (htj : (t * j) ^ 3 = 1) :
    ∃ Ψ : G ≃* M22, K.map Ψ.toMonoidHom = stabilizer M22 (0 : Fin 22) ∧
      H.map Ψ.toMonoidHom = m22HexStab := by
  obtain ⟨I, hI⟩ := exists_subgroup_doubleCoset Φ htt ht hj hj₁ hjj htj
  have hKI : K ≤ I := fun k hk => (hI k).mpr (Or.inl hk)
  have hHI : H ≤ I := by
    intro h hh
    refine (hI h).mpr ?_
    rcases hHt h hh with h1 | ⟨a, ha, b, hb, rfl⟩
    · exact Or.inl h1
    · exact Or.inr ⟨a, (Subgroup.mem_inf.mp ha).2, b, (Subgroup.mem_inf.mp hb).2, rfl⟩
  have hItop : ⊤ ≤ I := by
    rw [← hgen]
    exact sup_le hKI hHI
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  exact nonempty_mulEquiv_m22_of_witt Φ (fun k => by rw [htinv]; exact ht k)
    (fun g => (hI g).mp (hItop (Subgroup.mem_top g))) hH hH6

end CFSG.Quasithin.M22Witt
