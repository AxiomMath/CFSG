module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDSlChain

public section

namespace CFSG.StandardType.QTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Sl

theorem ne_of_dTau_fix (m : ℕ) (ε : Bool) {a b c : Fin m} (hab : a ≠ b)
    (h : dTau m ε a b (dBasis m c) = dBasis m c) : c ≠ a ∧ c ≠ b := by
  have hsg : sg ε ≠ 0 := by
    rcases sg_cases ε with h0 | h0 <;> rw [h0] <;> decide
  refine ⟨fun hca => ?_, fun hcb => ?_⟩
  · rw [hca, dTau_apply_left m ε hab] at h
    have h1 := congrFun h b
    simp only [Pi.smul_apply, dBasis_apply, if_true, smul_eq_mul, mul_one,
      if_neg hab.symm] at h1
    exact hsg h1
  · rw [hcb, dTau_apply_right m ε hab] at h
    have h1 := congrFun h a
    simp only [Pi.smul_apply, dBasis_apply, if_true, smul_eq_mul, mul_one, if_neg hab] at h1
    exact hsg h1

theorem exists_conj_pair_of_noncomm_fix {m : ℕ} (hm : 6 ≤ m) {a b a' b' c : Fin m}
    (hab : a ≠ b) (hab' : a' ≠ b') (ε₁ ε₂ : Bool)
    (hnc : dTau m ε₁ a b * dTau m ε₂ a' b' ≠ dTau m ε₂ a' b' * dTau m ε₁ a b)
    (hca : c ≠ a) (hcb : c ≠ b) (hca' : c ≠ a') (hcb' : c ≠ b') :
    ∃ p₀ p₁ p₂ : Fin m, p₁.val = p₀.val + 1 ∧ p₂.val = p₀.val + 2 ∧
      (p₀.val = 0 ∨ p₀.val = 3) ∧ c ≠ p₀ ∧ c ≠ p₁ ∧ c ≠ p₂ ∧
      ∃ U ∈ dEven m, (∃ κ : ZMod 3, (κ = 1 ∨ κ = -1) ∧ U (dBasis m c) = κ • dBasis m c) ∧
        U * dTau m false p₀ p₁ * U⁻¹ = dTau m ε₁ a b ∧
        U * dTau m false p₁ p₂ * U⁻¹ = dTau m ε₂ a' b' := by
  obtain ⟨y, x, z, hyx, hxz, hyz, hX, hY⟩ := exists_chain m hab hab' ε₁ ε₂ hnc
  have hXc : dTau m ε₁ y x (dBasis m c) = dBasis m c := by
    rw [← hX]
    exact dTau_apply_of_ne m ε₁ hca hcb
  have hYc : dTau m ε₂ x z (dBasis m c) = dBasis m c := by
    rw [← hY]
    exact dTau_apply_of_ne m ε₂ hca' hcb'
  obtain ⟨hcy, hcx⟩ := ne_of_dTau_fix m ε₁ hyx hXc
  obtain ⟨-, hcz⟩ := ne_of_dTau_fix m ε₂ hxz hYc
  by_cases hc3 : c.val < 3
  · let p₀ : Fin m := ⟨3, by omega⟩
    let p₁ : Fin m := ⟨4, by omega⟩
    let p₂ : Fin m := ⟨5, by omega⟩
    let p₃ : Fin m := ⟨0, by omega⟩
    have hc0 : c ≠ p₀ := Fin.ne_of_val_ne (by simp [p₀]; omega)
    have hc1 : c ≠ p₁ := Fin.ne_of_val_ne (by simp [p₁]; omega)
    have hc2 : c ≠ p₂ := Fin.ne_of_val_ne (by simp [p₂]; omega)
    obtain ⟨U, hU, hUfix, h1, h2⟩ := exists_conj_pair_fix m
      (p₀ := p₀) (p₁ := p₁) (p₂ := p₂) (p₃ := p₃)
      (Fin.ne_of_val_ne (by simp [p₀, p₁])) (Fin.ne_of_val_ne (by simp [p₀, p₂]))
      (Fin.ne_of_val_ne (by simp [p₀, p₃])) (Fin.ne_of_val_ne (by simp [p₁, p₂]))
      (Fin.ne_of_val_ne (by simp [p₁, p₃])) (Fin.ne_of_val_ne (by simp [p₂, p₃]))
      hyx hxz hyz hc0 hc1 hc2 hcy hcx hcz ε₁ ε₂
    exact ⟨p₀, p₁, p₂, rfl, rfl, Or.inr rfl, hc0, hc1, hc2, U, hU, hUfix, by rw [h1, ← hX],
      by rw [h2, ← hY]⟩
  · let p₀ : Fin m := ⟨0, by omega⟩
    let p₁ : Fin m := ⟨1, by omega⟩
    let p₂ : Fin m := ⟨2, by omega⟩
    let p₃ : Fin m := ⟨3, by omega⟩
    have hc0 : c ≠ p₀ := Fin.ne_of_val_ne (by simp [p₀]; omega)
    have hc1 : c ≠ p₁ := Fin.ne_of_val_ne (by simp [p₁]; omega)
    have hc2 : c ≠ p₂ := Fin.ne_of_val_ne (by simp [p₂]; omega)
    obtain ⟨U, hU, hUfix, h1, h2⟩ := exists_conj_pair_fix m
      (p₀ := p₀) (p₁ := p₁) (p₂ := p₂) (p₃ := p₃)
      (Fin.ne_of_val_ne (by simp [p₀, p₁])) (Fin.ne_of_val_ne (by simp [p₀, p₂]))
      (Fin.ne_of_val_ne (by simp [p₀, p₃])) (Fin.ne_of_val_ne (by simp [p₁, p₂]))
      (Fin.ne_of_val_ne (by simp [p₁, p₃])) (Fin.ne_of_val_ne (by simp [p₂, p₃]))
      hyx hxz hyz hc0 hc1 hc2 hcy hcx hcz ε₁ ε₂
    exact ⟨p₀, p₁, p₂, rfl, rfl, Or.inl rfl, hc0, hc1, hc2, U, hU, hUfix, by rw [h1, ← hX],
      by rw [h2, ← hY]⟩

end Sl

end CFSG.StandardType.QTwo

end
