module

public import CFSG.Quasithin.Vol2.Ch4Sec3Sp4Mat

public section

namespace CFSG.Quasithin.H13.Ch4.Sp4

open Matrix

variable {F : Type} [Field F]

theorem mulVec_inl (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (v : Fin 2 ⊕ Fin 2 → F)
    (i : Fin 2) : (M *ᵥ v) (Sum.inl i) =
      (M.toBlocks₁₁ *ᵥ (v ∘ Sum.inl)) i + (M.toBlocks₁₂ *ᵥ (v ∘ Sum.inr)) i := by
  conv_lhs => rw [← fromBlocks_toBlocks M]
  rw [fromBlocks_mulVec]
  rfl

theorem exists_ne_zero_ne_one [Fintype F] (hF : Fintype.card F = 4) : ∃ c : F, c ≠ 0 ∧ c ≠ 1 := by
  classical
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset F) ⊆ ({0, 1} : Finset F) := fun l _ => by
    by_cases hl : l = 0
    · simp [hl]
    · simp [h l hl]
  have h5 := Finset.card_le_card hsub
  rw [Finset.card_univ, hF] at h5
  have h6 := Finset.card_insert_le (0 : F) ({1} : Finset F)
  rw [Finset.card_singleton] at h6
  omega

variable [Fintype F] {W : Submodule F (Fin 2 ⊕ Fin 2 → F)} {Λ : Type} [Group Λ] [Finite Λ]
  {f : Λ →* GL (Fin 2 ⊕ Fin 2) F}

theorem LeviData.eq_zero_of_forall_mulVec_eq (d : LeviData F W f) {v : Fin 2 ⊕ Fin 2 → F}
    (hv : ∀ x, (f x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v = v) : v = 0 := by
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one d.card
  have hvW : v ∈ W := by
    by_contra hvW
    have hcv : c₀ • v ∉ W := fun h => hvW (by
      have := W.smul_mem c₀⁻¹ h
      rwa [smul_smul, inv_mul_cancel₀ hc0, one_smul] at this)
    obtain ⟨x, hx⟩ := d.exists_mulVec_sub_mem v (c₀ • v) hvW hcv
    rw [hv x] at hx
    have h1 : (1 - c₀) • v ∈ W := by rwa [sub_smul, one_smul]
    have := W.smul_mem (1 - c₀)⁻¹ h1
    rw [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr (Ne.symm hc1)), one_smul] at this
    exact hvW this
  obtain ⟨g, -, hmem, -, h21, hsurj⟩ := d.exists_std
  set gi : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
    ((g⁻¹ : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) with hgi
  have hgg : ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ
      (gi *ᵥ v) = v := by
    rw [hgi, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]
  have hw : gi *ᵥ v ∈ stdPlane F := (hmem v).mp hvW
  have hwr : (gi *ᵥ v) ∘ Sum.inr = 0 := funext fun j => mem_stdPlane.mp hw j
  have hfix : ∀ x, (conjHom g f x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ (gi *ᵥ v) =
      gi *ᵥ v := by
    intro x
    rw [conjHom_apply, Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, hgg, hv x]
  have hA : ∀ x, ((slHom (conjHom g f) h21 d.perf x : SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) *ᵥ ((gi *ᵥ v) ∘ Sum.inl) = (gi *ᵥ v) ∘ Sum.inl := by
    intro x
    funext i
    have h := congrFun (hfix x) (Sum.inl i)
    rw [mulVec_inl, hwr, mulVec_zero, Pi.zero_apply, add_zero] at h
    rw [coe_slHom]
    exact h
  by_cases ha0 : (gi *ᵥ v) ∘ Sum.inl = 0
  · have h0 : gi *ᵥ v = 0 := by
      funext k
      cases k with
      | inl i => exact congrFun ha0 i
      | inr j => exact congrFun hwr j
    rw [← hgg, h0, mulVec_zero]
  · exfalso
    obtain ⟨A, hAa⟩ := exists_sl2_mulVec _ (c₀ • ((gi *ᵥ v) ∘ Sum.inl)) ha0 (smul_ne_zero hc0 ha0)
    obtain ⟨x, hx⟩ := hsurj A
    have h := hA x
    rw [hx, hAa] at h
    apply ha0
    have h2 : (c₀ - 1) • ((gi *ᵥ v) ∘ Sum.inl) = 0 := by rw [sub_smul, one_smul, h, sub_self]
    exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hc1)

end CFSG.Quasithin.H13.Ch4.Sp4
