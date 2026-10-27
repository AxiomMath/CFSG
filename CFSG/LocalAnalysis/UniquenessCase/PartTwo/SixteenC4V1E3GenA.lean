module

public import CFSG.ClassicalGroups.Unitary.Elements

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.ClassicalGroups.Unitary Matrix
open CFSG.LieType.Universal.Unitary (SUid)

variable {F : Type} [Field F] [Finite F] {σ : F ≃+* F}

theorem s16c4v1e3_exists_dual_pair (hσ : IsUnitaryInvolution σ) {u₁ u₂ : Fin 4 → F}
    (hli : ∀ a b : F, a • u₁ + b • u₂ = 0 → a = 0 ∧ b = 0)
    (h11 : herm σ u₁ u₁ = 0) (h12 : herm σ u₁ u₂ = 0) (h22 : herm σ u₂ u₂ = 0) :
    ∃ y₁ y₂ : Fin 4 → F, herm σ y₁ y₁ = 0 ∧ herm σ y₂ y₂ = 0 ∧ herm σ y₁ y₂ = 0 ∧
      herm σ u₁ y₁ = 1 ∧ herm σ u₁ y₂ = 0 ∧ herm σ u₂ y₁ = 0 ∧ herm σ u₂ y₂ = 1 := by
  let Φ : (Fin 4 → F) →ₗ[F] F × F := (hermL σ u₁).prod (hermL σ u₂)
  have hΦapply : ∀ z, Φ z = (herm σ u₁ z, herm σ u₂ z) := fun _ => rfl
  have hΦtop : LinearMap.range Φ = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top (LinearMap.range Φ)
      (lt_top_iff_ne_top.mpr hne)
    have hφ_apply : ∀ p q : F, φ (p, q) = p * φ (1, 0) + q * φ (0, 1) := by
      intro p q
      have hpq : (p, q) = p • (1, 0) + q • (0, 1) := by ext <;> simp
      rw [hpq, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have hlin : ∀ y, herm σ u₁ y * φ (1, 0) + herm σ u₂ y * φ (0, 1) = 0 := by
      intro y
      have h : φ (Φ y) = 0 := by
        have := hφ ⟨y, rfl⟩
        simpa only [LinearMap.mem_ker] using this
      rw [hΦapply y, hφ_apply] at h
      exact h
    have hvec : σ.symm (φ (1, 0)) • u₁ + σ.symm (φ (0, 1)) • u₂ = 0 := by
      apply eq_zero_of_herm σ
      intro y
      rw [herm_add_left, herm_smul_left, herm_smul_left]
      simp only [RingEquiv.apply_symm_apply]
      rw [mul_comm (φ (1, 0)) (herm σ u₁ y), mul_comm (φ (0, 1)) (herm σ u₂ y)]
      exact hlin y
    have ha0 : φ (1, 0) = 0 := by
      have h1 : σ.symm (φ (1, 0)) = 0 :=
        (hli (σ.symm (φ (1, 0))) (σ.symm (φ (0, 1))) hvec).1
      have h := congrArg σ h1
      rw [RingEquiv.apply_symm_apply, map_zero] at h
      exact h
    have hb0 : φ (0, 1) = 0 := by
      have h2 : σ.symm (φ (0, 1)) = 0 :=
        (hli (σ.symm (φ (1, 0))) (σ.symm (φ (0, 1))) hvec).2
      have h := congrArg σ h2
      rw [RingEquiv.apply_symm_apply, map_zero] at h
      exact h
    have hφzero : φ = 0 := by
      apply LinearMap.ext
      intro p
      obtain ⟨p1, p2⟩ := p
      rw [hφ_apply, ha0, hb0]
      simp
    exact hφ0 hφzero
  have hsurj : ∀ p q : F, ∃ z, herm σ u₁ z = p ∧ herm σ u₂ z = q := by
    intro p q
    have hmem : (p, q) ∈ LinearMap.range Φ := by rw [hΦtop]; exact Submodule.mem_top
    rw [LinearMap.mem_range] at hmem
    obtain ⟨z, hz⟩ := hmem
    rw [hΦapply z] at hz
    exact ⟨z, by simpa using congrArg Prod.fst hz, by simpa using congrArg Prod.snd hz⟩
  obtain ⟨z₁, hz11, hz21⟩ := hsurj 1 0
  obtain ⟨z₂, hz12, hz22⟩ := hsurj 0 1
  have hz₁u₁ : herm σ z₁ u₁ = 1 := by rw [herm_conj σ hσ.invol, hz11, map_one]
  have hz₂u₁ : herm σ z₂ u₁ = 0 := by rw [herm_conj σ hσ.invol, hz12, map_zero]
  have hz₁u₂ : herm σ z₁ u₂ = 0 := by rw [herm_conj σ hσ.invol, hz21, map_zero]
  have hz₂u₂ : herm σ z₂ u₂ = 1 := by rw [herm_conj σ hσ.invol, hz22, map_one]
  have hu21 : herm σ u₂ u₁ = 0 := herm_eq_zero_comm σ hσ.invol h12
  obtain ⟨c₁₁, hc₁₁⟩ := hσ.trace_surj (-(herm σ z₁ z₁))
    (by rw [map_neg, herm_self_fixed σ hσ.invol])
  obtain ⟨c₂₂, hc₂₂⟩ := hσ.trace_surj (-(herm σ z₂ z₂))
    (by rw [map_neg, herm_self_fixed σ hσ.invol])
  refine ⟨z₁ + c₁₁ • u₁, z₂ + (-(herm σ z₁ z₂)) • u₁ + c₂₂ • u₂,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h : herm σ (z₁ + c₁₁ • u₁) (z₁ + c₁₁ • u₁)
        = herm σ z₁ z₁ + (c₁₁ + σ c₁₁) := by
      simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, h11, hz11,
        hz₁u₁, mul_one, mul_zero, add_zero, zero_add]
      ring
    rw [h, hc₁₁, add_neg_cancel]
  · have h : herm σ (z₂ + (-(herm σ z₁ z₂)) • u₁ + c₂₂ • u₂)
        (z₂ + (-(herm σ z₁ z₂)) • u₁ + c₂₂ • u₂) = herm σ z₂ z₂ + (c₂₂ + σ c₂₂) := by
      simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, h11, h12, h22,
        hu21, hz12, hz22, hz₂u₁, hz₂u₂, mul_one, mul_zero, add_zero, zero_add]
      ring
    rw [h, hc₂₂, add_neg_cancel]
  · have h : herm σ (z₁ + c₁₁ • u₁) (z₂ + (-(herm σ z₁ z₂)) • u₁ + c₂₂ • u₂)
        = herm σ z₁ z₂ + -(herm σ z₁ z₂) := by
      simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, h11, h12,
        hz11, hz12, hz₁u₁, hz₁u₂, mul_one, mul_zero, add_zero, zero_add]
    rw [h, add_neg_cancel]
  · simp only [herm_add_right, herm_smul_right, h11, hz11, mul_zero, add_zero]
  · simp only [herm_add_right, herm_smul_right, h11, h12, hz12, mul_zero, add_zero, zero_add]
  · simp only [herm_add_right, herm_smul_right, hu21, hz21, mul_zero, add_zero]
  · simp only [herm_add_right, herm_smul_right, hu21, h22, hz22, mul_zero, add_zero, zero_add]

theorem s16c4v1e3_opposite_of_dual_pair (hσ : IsUnitaryInvolution σ) {u₁ u₂ y₁ y₂ : Fin 4 → F}
    (h11 : herm σ u₁ u₁ = 0) (h12 : herm σ u₁ u₂ = 0) (h22 : herm σ u₂ u₂ = 0)
    (hy₁ : herm σ y₁ y₁ = 0) (hy₂ : herm σ y₂ y₂ = 0) (hy₁₂ : herm σ y₁ y₂ = 0)
    (hd₁₁ : herm σ u₁ y₁ = 1) (hd₁₂ : herm σ u₁ y₂ = 0) (hd₂₁ : herm σ u₂ y₁ = 0)
    (hd₂₂ : herm σ u₂ y₂ = 1) :
    ∃ g : ↥(SUid σ 4), ∀ a b : F, (a ≠ 0 ∨ b ≠ 0) → ∃ a' b' : F,
      herm σ (a • u₁ + b • u₂) (g • (a' • u₁ + b' • u₂)) ≠ 0 := by
  obtain ⟨τ, hτ0, hτ⟩ := hσ.exists_traceZero
  have hu21 : herm σ u₂ u₁ = 0 := herm_eq_zero_comm σ hσ.invol h12
  have hy1u1 : herm σ y₁ u₁ = 1 := by rw [herm_conj σ hσ.invol, hd₁₁, map_one]
  have hy2u1 : herm σ y₂ u₁ = 0 := by rw [herm_conj σ hσ.invol, hd₁₂, map_zero]
  have hy1u2 : herm σ y₁ u₂ = 0 := by rw [herm_conj σ hσ.invol, hd₂₁, map_zero]
  have hy2u2 : herm σ y₂ u₂ = 1 := by rw [herm_conj σ hσ.invol, hd₂₂, map_one]
  have ht2u1 : tv hσ.invol hy₂ hτ • u₁ = u₁ := by
    rw [tv_smul, hy2u1, mul_zero, zero_smul, add_zero]
  have ht2u2 : tv hσ.invol hy₂ hτ • u₂ = u₂ + τ • y₂ := by
    rw [tv_smul, hy2u2, mul_one]
  have ht1u1 : tv hσ.invol hy₁ hτ • u₁ = u₁ + τ • y₁ := by
    rw [tv_smul, hy1u1, mul_one]
  have ht1y2 : tv hσ.invol hy₁ hτ • (u₂ + τ • y₂) = u₂ + τ • y₂ := by
    have h0 : herm σ y₁ (u₂ + τ • y₂) = 0 := by
      rw [herm_add_right, herm_smul_right, hy1u2, hy₁₂, mul_zero, add_zero]
    rw [tv_smul, h0, mul_zero, zero_smul, add_zero]
  have hgy1 : (tv hσ.invol hy₁ hτ * tv hσ.invol hy₂ hτ) • u₁ = u₁ + τ • y₁ := by
    rw [mul_smul, ht2u1, ht1u1]
  have hgy2 : (tv hσ.invol hy₁ hτ * tv hσ.invol hy₂ hτ) • u₂ = u₂ + τ • y₂ := by
    rw [mul_smul, ht2u2, ht1y2]
  refine ⟨tv hσ.invol hy₁ hτ * tv hσ.invol hy₂ hτ, ?_⟩
  intro a b hab
  rcases eq_or_ne a 0 with ha | ha
  · have hb : b ≠ 0 := by
      rcases hab with h | h
      · exact (h ha).elim
      · exact h
    refine ⟨0, 1, ?_⟩
    have hw : a • u₁ + b • u₂ = b • u₂ := by rw [ha, zero_smul, zero_add]
    rw [hw, zero_smul, one_smul, zero_add, hgy2]
    have hval : herm σ (b • u₂) (u₂ + τ • y₂) = σ b * τ := by
      simp only [herm_smul_left, herm_add_right, herm_smul_right, h22, hd₂₂, mul_one, mul_zero,
        add_zero, zero_add]
      ring
    rw [hval]
    exact mul_ne_zero (fun h => hb (σ.injective (by rw [h, map_zero]))) hτ0
  · refine ⟨1, 0, ?_⟩
    rw [one_smul, zero_smul, add_zero, hgy1]
    have hval : herm σ (a • u₁ + b • u₂) (u₁ + τ • y₁) = σ a * τ := by
      simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, h11, hu21,
        hd₁₁, hd₂₁, mul_one, mul_zero, add_zero, zero_add]
      ring
    rw [hval]
    exact mul_ne_zero (fun h => ha (σ.injective (by rw [h, map_zero]))) hτ0

theorem s16c4v1e3_exists_opposite (hσ : IsUnitaryInvolution σ) {W : Submodule F (Fin 4 → F)}
    (hW : Module.finrank F ↥W = 2) (hti : ∀ u ∈ W, ∀ u' ∈ W, herm σ u u' = 0) :
    ∃ g : ↥(SUid σ 4), ∀ w ∈ W, w ≠ 0 → ∃ w' ∈ W, herm σ w (g • w') ≠ 0 := by
  haveI : Module.Finite F ↥W := Module.finite_of_finrank_pos (by rw [hW]; norm_num)
  let b : Module.Basis (Fin 2) F ↥W := Module.finBasisOfFinrankEq F ↥W hW
  have hb_li : LinearIndependent F ![b 0, b 1] := by
    have hb : ![b 0, b 1] = b := by funext i; fin_cases i <;> rfl
    rw [hb]; exact b.linearIndependent
  have hpair := LinearIndependent.pair_iff.mp hb_li
  have hli : ∀ a c : F, a • (b 0 : Fin 4 → F) + c • (b 1 : Fin 4 → F) = 0 →
      a = 0 ∧ c = 0 := by
    intro a c hac
    refine hpair a c ?_
    apply Subtype.ext
    simpa using hac
  have h11 : herm σ (b 0 : Fin 4 → F) (b 0 : Fin 4 → F) = 0 := hti _ (b 0).2 _ (b 0).2
  have h12 : herm σ (b 0 : Fin 4 → F) (b 1 : Fin 4 → F) = 0 := hti _ (b 0).2 _ (b 1).2
  have h22 : herm σ (b 1 : Fin 4 → F) (b 1 : Fin 4 → F) = 0 := hti _ (b 1).2 _ (b 1).2
  obtain ⟨y₁, y₂, hy₁, hy₂, hy₁₂, hd₁₁, hd₁₂, hd₂₁, hd₂₂⟩ :=
    s16c4v1e3_exists_dual_pair hσ hli h11 h12 h22
  obtain ⟨g, hg⟩ := s16c4v1e3_opposite_of_dual_pair hσ h11 h12 h22 hy₁ hy₂ hy₁₂
    hd₁₁ hd₁₂ hd₂₁ hd₂₂
  refine ⟨g, ?_⟩
  intro w hw hw0
  set a : F := b.repr ⟨w, hw⟩ 0 with ha
  set c : F := b.repr ⟨w, hw⟩ 1 with hc
  have hwW : (⟨w, hw⟩ : ↥W) = a • (b 0 : ↥W) + c • (b 1 : ↥W) := by
    have hsum := b.sum_repr ⟨w, hw⟩
    rw [Fin.sum_univ_two] at hsum
    rw [← hsum]
  have hwrepr : w = a • (b 0 : Fin 4 → F) + c • (b 1 : Fin 4 → F) := by
    have h := congrArg (Subtype.val) hwW
    simpa only [Submodule.coe_add, Submodule.coe_smul] using h
  have hac : a ≠ 0 ∨ c ≠ 0 := by
    rcases eq_or_ne a 0 with ha0 | ha0
    · refine Or.inr ?_
      intro hc0
      apply hw0
      rw [hwrepr, ha0, hc0, zero_smul, zero_smul, add_zero]
    · exact Or.inl ha0
  obtain ⟨a', c', hval⟩ := hg a c hac
  refine ⟨a' • (b 0 : Fin 4 → F) + c' • (b 1 : Fin 4 → F), ?_, ?_⟩
  · exact W.add_mem (W.smul_mem a' (b 0).2) (W.smul_mem c' (b 1).2)
  · rw [hwrepr]; exact hval

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
