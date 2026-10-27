module

public import CFSG.Quasithin.MS93.S5ACoc
public import CFSG.Quasithin.MS93.MSPHeis

public section

namespace CFSG.Quasithin.MS93.S33

open CFSG.Quasithin CFSG.Quasithin.JonesParshall MSP Matrix

variable {F : Type} [Field F] [Fintype F] [CharP F 2]

omit [Fintype F] [CharP F 2] in
theorem transvMat_apply (x : V4 F) (c : F) (i j : Fin 2 ⊕ Fin 2) :
    transvMat x c i j = (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) i j +
      c * form F x (Pi.single j 1) * x i := by
  have h := congrFun (transvMat_mulVec x c (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one, Matrix.col_apply] at h
  rw [h]
  simp [Matrix.one_apply, Pi.single_apply]

theorem sqf_transv_e₁ (s : F) : S5.sqf (mat (transv (e₁ F) s)) = sqrtF s • e₁ F := by
  have hm : mat (transv (e₁ F) s) = transvMat (e₁ F) s := mat_ofMat _ _ _ _ _
  funext i
  simp only [S5.sqf, hm, Pi.smul_apply, smul_eq_mul]
  rcases i with i | i <;> fin_cases i <;>
    simp [quadQ, transvMat_apply, form_e₁, sqrtF_zero]

omit [CharP F 2] in
theorem exists_ne_zero_ne_one (hF : 2 < Fintype.card F) : ∃ s : F, s ≠ 0 ∧ s ≠ 1 := by
  classical
  by_contra hall
  push Not at hall
  have hsub : (Finset.univ : Finset F) ⊆ {0, 1} := fun s _ => by
    by_cases hs : s = 0
    · simp [hs]
    · simp [hall s hs]
  have := Finset.card_le_card hsub
  rw [Finset.card_univ] at this
  have h2 : ({0, 1} : Finset F).card ≤ 2 := Finset.card_le_two
  omega

theorem coboundary_of_vanish_X₂ {k : ℕ} (hF : Fintype.card F = 2 ^ k) (hk : 2 ≤ k)
    {φ : Sp4 F → V4 F} (hφ : ∀ g h, φ (g * h) = φ g + mat g *ᵥ φ h)
    (h0 : ∀ s : F, φ (transv (e₁ F) s) = 0) :
    ∃ m : V4 F, ∀ g, φ g = mat g *ᵥ m - m := by
  obtain ⟨B, m, hBm⟩ := S5.exists_eq_sqf hF (by omega) hφ
  have hval : ∀ s : F, B * sqrtF s + s * m (.inr 0) = 0 := fun s => by
    have h := congrFun ((hBm _).symm.trans (h0 s)) (.inl 0)
    rw [sqf_transv_e₁, transv_mulVec, form_e₁] at h
    simpa using h
  have hF3 : 2 < Fintype.card F := by
    rw [hF]
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  obtain ⟨s, hs0, hs1⟩ := exists_ne_zero_ne_one hF3
  have h1 := hval 1
  rw [sqrtF_one, mul_one, one_mul] at h1
  have hm : m (.inr 0) = B := by
    rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h1
    exact h1.symm
  have hs := hval s
  rw [hm] at hs
  have hB : B = 0 := by
    by_contra hB
    have h2 : sqrtF s + s = 0 := by
      have : B * (sqrtF s + s) = 0 := by rw [mul_add]; rw [mul_comm s B] at hs; exact hs
      exact (mul_eq_zero.1 this).resolve_left hB
    have h3 : sqrtF s = s := by rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h2; exact h2
    have h4 : s ^ 2 = s := by
      calc s ^ 2 = sqrtF s ^ 2 := by rw [h3]
        _ = s := sqrtF_sq s
    have h5 : s * (s - 1) = 0 := by rw [mul_sub, mul_one, ← sq, h4, sub_self]
    rcases mul_eq_zero.1 h5 with h | h
    · exact hs0 h
    · exact hs1 (sub_eq_zero.1 h)
  refine ⟨m, fun g => ?_⟩
  rw [hBm g, hB, zero_smul, zero_add]

theorem coboundary_of_vanish_xPoint {k : ℕ} (hF : Fintype.card F = 2 ^ k) (hk : 2 ≤ k)
    {p : Submodule F (V4 F)} (hp : IsPoint p) {φ : Sp4 F → V4 F}
    (hφ : ∀ g h, φ (g * h) = φ g + mat g *ᵥ φ h) (h0 : ∀ t ∈ xPoint p, φ t = 0) :
    ∃ m : V4 F, ∀ g, φ g = mat g *ᵥ m - m := by
  obtain ⟨g₀, hg₀⟩ := exists_map_pt₀_eq hp
  set φ' : Sp4 F → V4 F := fun γ => mat g₀⁻¹ *ᵥ φ (g₀ * γ * g₀⁻¹) with hφ'
  have hφ'c : ∀ γ γ', φ' (γ * γ') = φ' γ + mat γ *ᵥ φ' γ' := fun γ γ' => by
    have e : g₀ * (γ * γ') * g₀⁻¹ = (g₀ * γ * g₀⁻¹) * (g₀ * γ' * g₀⁻¹) := by group
    simp only [hφ']
    rw [e, hφ, mulVec_add, ← mat_mul_mulVec, ← mat_mul_mulVec]
    congr 2
    group
  have h0' : ∀ s : F, φ' (transv (e₁ F) s) = 0 := fun s => by
    have hmem : g₀ * transv (e₁ F) s * g₀⁻¹ ∈ xPoint p := by
      rw [← hg₀, ← X₂_map_conj]
      exact ⟨transv (e₁ F) s, transv_mem_X₂ s, rfl⟩
    simp only [hφ', h0 _ hmem, mulVec_zero]
  obtain ⟨m, hm⟩ := coboundary_of_vanish_X₂ hF hk hφ'c h0'
  refine ⟨mat g₀ *ᵥ m, fun g => ?_⟩
  have h := hm (g₀⁻¹ * g * g₀)
  simp only [hφ'] at h
  have e : g₀ * (g₀⁻¹ * g * g₀) * g₀⁻¹ = g := by group
  rw [e] at h
  have h2 := congrArg (mat g₀ *ᵥ ·) h
  simp only [mat_mulVec_inv, mulVec_sub] at h2
  rw [h2, ← mat_mul_mulVec, ← mat_mul_mulVec]
  congr 2
  group

end CFSG.Quasithin.MS93.S33
