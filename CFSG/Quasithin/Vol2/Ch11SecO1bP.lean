module

public import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.Quasithin.Background.JonesParshallSL3

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecO1b

open CFSG.Quasithin Matrix

theorem conjSubgroup_stabilizer {Γ α : Type*} [Group Γ] [MulAction Γ α] (a : α) (δ : Γ) :
    conjSubgroup (MulAction.stabilizer Γ a) δ = MulAction.stabilizer Γ (δ⁻¹ • a) := by
  ext γ
  rw [mem_conjSubgroup_iff, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
    mul_smul, mul_smul, smul_eq_iff_eq_inv_smul, eq_comm]

variable {K : Type} [Field K]

theorem sl3_smul_comm (A : SpecialLinearGroup (Fin 3) K) (c : K) (v : Fin 3 → K) :
    A • (c • v) = c • (A • v) := by
  rw [JonesParshall.smul3_def, JonesParshall.smul3_def, Matrix.mulVec_smul]

theorem exists_stab3_e0 {x : Fin 3 → K} (hx : ¬ (x 1 = 0 ∧ x 2 = 0)) :
    ∃ B ∈ MulAction.stabilizer (SpecialLinearGroup (Fin 3) K) (JonesParshall.e0 : Fin 3 → K),
      B • (![0, 1, 0] : Fin 3 → K) = x := by
  by_cases h1 : x 1 = 0
  · have h2 : x 2 ≠ 0 := fun h2 => hx ⟨h1, h2⟩
    refine ⟨⟨!![1, x 0, 0; 0, 0, -(x 2)⁻¹; 0, x 2, 0], by simp [Matrix.det_fin_three, h2]⟩,
      ?_, ?_⟩
    · change !![1, x 0, 0; 0, 0, -(x 2)⁻¹; 0, x 2, 0] *ᵥ JonesParshall.e0 = JonesParshall.e0
      refine JonesParshall.vec3_ext ?_ ?_ ?_ <;> rw [JonesParshall.mulVec3] <;>
        simp [JonesParshall.e0]
    · change !![1, x 0, 0; 0, 0, -(x 2)⁻¹; 0, x 2, 0] *ᵥ ![0, 1, 0] = x
      refine JonesParshall.vec3_ext ?_ ?_ ?_ <;> rw [JonesParshall.mulVec3] <;> simp [h1]
  · refine ⟨⟨!![1, x 0, 0; 0, x 1, 0; 0, x 2, (x 1)⁻¹], by simp [Matrix.det_fin_three, h1]⟩,
      ?_, ?_⟩
    · change !![1, x 0, 0; 0, x 1, 0; 0, x 2, (x 1)⁻¹] *ᵥ JonesParshall.e0 = JonesParshall.e0
      refine JonesParshall.vec3_ext ?_ ?_ ?_ <;> rw [JonesParshall.mulVec3] <;>
        simp [JonesParshall.e0]
    · change !![1, x 0, 0; 0, x 1, 0; 0, x 2, (x 1)⁻¹] *ᵥ ![0, 1, 0] = x
      refine JonesParshall.vec3_ext ?_ ?_ ?_ <;> rw [JonesParshall.mulVec3] <;> simp

theorem exists_stab3_smul_eq {u x y : Fin 3 → K} (hu : u ≠ 0) (hx : ∀ c : K, x ≠ c • u)
    (hy : ∀ c : K, y ≠ c • u) :
    ∃ γ ∈ MulAction.stabilizer (SpecialLinearGroup (Fin 3) K) u, γ • x = y := by
  obtain ⟨A, hA⟩ := MulAction.mem_orbit_iff.mp (JonesParshall.mulVec3_e0_mem_orbit u hu)
  have hout : ∀ z : Fin 3 → K, (∀ c : K, z ≠ c • u) → ¬ ((A⁻¹ • z) 1 = 0 ∧ (A⁻¹ • z) 2 = 0) := by
    rintro z hz ⟨h1, h2⟩
    apply hz ((A⁻¹ • z) 0)
    have h : A⁻¹ • z = (A⁻¹ • z) 0 • JonesParshall.e0 := by
      generalize A⁻¹ • z = w at h1 h2 ⊢
      refine JonesParshall.vec3_ext ?_ ?_ ?_ <;> simp [JonesParshall.e0, h1, h2]
    calc z = A • (A⁻¹ • z) := (smul_inv_smul A z).symm
      _ = A • ((A⁻¹ • z) 0 • JonesParshall.e0) := congrArg (A • ·) h
      _ = (A⁻¹ • z) 0 • u := by rw [sl3_smul_comm, hA]
  obtain ⟨Bx, hBx, hBxe⟩ := exists_stab3_e0 (hout x hx)
  obtain ⟨By, hBy, hBye⟩ := exists_stab3_e0 (hout y hy)
  rw [MulAction.mem_stabilizer_iff] at hBx hBy
  refine ⟨A * By * Bx⁻¹ * A⁻¹, ?_, ?_⟩
  · rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, mul_smul, ← hA, inv_smul_smul,
      inv_smul_eq_iff.mpr hBx.symm, hBy]
  · rw [mul_smul, mul_smul, mul_smul, ← hBxe, inv_smul_smul, hBye, smul_inv_smul]

theorem sup_stab3_eq_top {p₁ p₂ : Fin 3 → K} (hp₁ : p₁ ≠ 0) (hp₂ : p₂ ≠ 0)
    (h12 : ∀ c : K, p₂ ≠ c • p₁) :
    MulAction.stabilizer (SpecialLinearGroup (Fin 3) K) p₁ ⊔
      MulAction.stabilizer (SpecialLinearGroup (Fin 3) K) p₂ = ⊤ := by
  have h21 : ∀ c : K, p₁ ≠ c • p₂ := fun c h => by
    have hc : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at h
      exact hp₁ h
    exact h12 c⁻¹ (by rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul])
  have htr : ∀ v : Fin 3 → K, v ≠ 0 → ∃ h ∈ MulAction.stabilizer _ p₁ ⊔
      MulAction.stabilizer (SpecialLinearGroup (Fin 3) K) p₂, h • p₁ = v := by
    intro v hv
    by_cases hv2 : ∀ c : K, v ≠ c • p₂
    · obtain ⟨γ, hγ, hγv⟩ := exists_stab3_smul_eq hp₂ h21 hv2
      exact ⟨γ, Subgroup.mem_sup_right hγ, hγv⟩
    · push Not at hv2
      obtain ⟨c, hc⟩ := hv2
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [zero_smul] at hc
        exact hv hc
      have hw2 : ∀ d : K, p₁ + p₂ ≠ d • p₂ := fun d h =>
        h21 (d - 1) (by rw [sub_smul, one_smul, ← h, add_sub_cancel_right])
      have hw1 : ∀ d : K, p₁ + p₂ ≠ d • p₁ := fun d h =>
        h12 (d - 1) (by rw [sub_smul, one_smul, ← h, add_sub_cancel_left])
      have hv1 : ∀ d : K, v ≠ d • p₁ := fun d h =>
        h12 (c⁻¹ * d) (by rw [mul_smul, ← h, hc, smul_smul, inv_mul_cancel₀ hc0, one_smul])
      obtain ⟨γ₂, hγ₂, hγ₂w⟩ := exists_stab3_smul_eq hp₂ h21 hw2
      obtain ⟨γ₁, hγ₁, hγ₁v⟩ := exists_stab3_smul_eq hp₁ hw1 hv1
      exact ⟨γ₁ * γ₂, Subgroup.mul_mem _ (Subgroup.mem_sup_left hγ₁)
        (Subgroup.mem_sup_right hγ₂), by rw [mul_smul, hγ₂w, hγ₁v]⟩
  rw [eq_top_iff]
  intro A _
  obtain ⟨h, hh, hhA⟩ := htr (A • p₁) fun h0 => hp₁ (by rw [← inv_smul_smul A p₁, h0, smul_zero])
  have hs : h⁻¹ * A ∈ MulAction.stabilizer (SpecialLinearGroup (Fin 3) K) p₁ := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, ← hhA, inv_smul_smul]
  have h1 := Subgroup.mul_mem _ hh (Subgroup.mem_sup_left hs)
  rwa [mul_inv_cancel_left] at h1

end CFSG.Quasithin.Vol2.Ch11.SecO1b
