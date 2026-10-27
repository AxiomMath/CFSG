module

public import CFSG.LocalAnalysis.StandardType.FS81.OddCoreOrthP

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

theorem spMat_mulVec_single {k : ℕ} (σ : Equiv.Perm (Fin k)) (s : Fin k → ZMod 3) (j : Fin k)
    (c : ZMod 3) : spMat σ s *ᵥ Pi.single j c = Pi.single (σ j) (s j * c) := by
  rw [spMat_mulVec]
  funext i
  by_cases h : i = σ j
  · subst h
    simp
  · have h' : σ.symm i ≠ j := fun h'' => h (by rw [← h'', Equiv.apply_symm_apply])
    simp [h, h']

theorem spMat_mulVec_e0 {n : ℕ} {σ : Equiv.Perm (Fin (n + 1))} {s : Fin (n + 1) → ZMod 3}
    (hσ : σ 0 = 0) (hs : s 0 = 1) : spMat σ s *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  rw [spMat_mulVec_single, hσ, hs, one_mul]

theorem perm_mem_evenFix0 {n : ℕ} (σ : Equiv.Perm (Fin (n + 1))) (hσ : σ 0 = 0) :
    spMat σ (fun _ => 1) ∈ evenFix0 n :=
  ⟨σ, fun _ => 1, fun _ => Or.inl rfl, ⟨hσ, rfl, by simp⟩, rfl⟩

theorem gl_mul_self {k : ℕ} {x : GL (Fin k) (ZMod 3)} {σ : Equiv.Perm (Fin k)}
    {s : Fin k → ZMod 3} (hx : (x : Matrix (Fin k) (Fin k) (ZMod 3)) = spMat σ s)
    (hσ : σ * σ = 1) (hs : ∀ j, s (σ j) * s j = 1) : x * x = 1 :=
  Units.ext (by rw [Units.val_mul, hx, Units.val_one]; exact spMat_mul_self σ s hσ hs)

theorem orth_eq_bot_twD7 {Xg Mg : Subgroup (GL (Fin (7 + 1)) (ZMod 3))}
    (hC : ∀ x ∈ Xg, (x : Matrix (Fin (7 + 1)) (Fin (7 + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
      Pi.single 0 1 → (x : Matrix (Fin (7 + 1)) (Fin (7 + 1)) (ZMod 3)) ∈ monoFix0 7)
    (hW : ∀ A ∈ evenFix0 7, ∃ x ∈ Xg, (x : Matrix (Fin (7 + 1)) (Fin (7 + 1)) (ZMod 3)) = A)
    (hMX : Mg ≤ Xg) (hMn : ∀ g ∈ Xg, ∀ m ∈ Mg, g * m * g⁻¹ ∈ Mg)
    (hMc : ∀ a ∈ Mg, ∀ b ∈ Mg, a * b = b * a)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hMp : ∀ m ∈ Mg, m ^ p = 1) : Mg = ⊥ := by
  set T₁ : Finset (Fin (7 + 1)) := {1, 2, 3, 4, 5, 6} with hT₁
  set T₂ : Finset (Fin (7 + 1)) := {2, 3, 4, 5, 6, 7} with hT₂
  obtain ⟨s₁, hs₁X, hs₁⟩ := hW _ (sgnOn_mem_evenFix0 T₁ (by decide) (by decide))
  obtain ⟨s₂, hs₂X, hs₂⟩ := hW _ (sgnOn_mem_evenFix0 T₂ (by decide) (by decide))
  obtain ⟨z₁, hz₁X, hz₁⟩ := hW _ (perm_mem_evenFix0 (Equiv.swap 2 7) (by decide))
  obtain ⟨z₂, hz₂X, hz₂⟩ := hW _ (perm_mem_evenFix0 (Equiv.swap 1 3 * Equiv.swap 4 7) (by decide))
  obtain ⟨z₃, hz₃X, hz₃⟩ := hW _ (perm_mem_evenFix0 (Equiv.swap 1 5 * Equiv.swap 6 7) (by decide))
  have hz₁i : z₁⁻¹ = z₁ := inv_eq_of_mul_eq_one_right (gl_mul_self hz₁ (by decide) (by decide))
  have hz₂i : z₂⁻¹ = z₂ := inv_eq_of_mul_eq_one_right (gl_mul_self hz₂ (by decide) (by decide))
  have hz₃i : z₃⁻¹ = z₃ := inv_eq_of_mul_eq_one_right (gl_mul_self hz₃ (by decide) (by decide))
  have hinv₁ : ∀ m ∈ Mg, s₁ * m * s₁⁻¹ = m⁻¹ := fun m hm =>
    orth_inverts (n := 7) (by norm_num) hC hW hMX hMn hMc hp hp5 hMp hs₁X
      (gl_mul_self hs₁ (by decide) (by decide)) (by rw [hs₁]; exact spMat_mulVec_e0 rfl rfl)
      (w := Pi.single 7 1) (fun v hv => by
        rw [hs₁] at hv
        have hz : ∀ i ∈ T₁, v i = 0 := fun i hi => eq_zero_of_mulVec_sgnOn hv hi
        refine ⟨v 0, v 7, funext fun i => ?_⟩
        fin_cases i <;> simp [hz, hT₁]) hm
  have hinv₂ : ∀ m ∈ Mg, s₂ * m * s₂⁻¹ = m⁻¹ := fun m hm =>
    orth_inverts (n := 7) (by norm_num) hC hW hMX hMn hMc hp hp5 hMp hs₂X
      (gl_mul_self hs₂ (by decide) (by decide)) (by rw [hs₂]; exact spMat_mulVec_e0 rfl rfl)
      (w := Pi.single 1 1) (fun v hv => by
        rw [hs₂] at hv
        have hz : ∀ i ∈ T₂, v i = 0 := fun i hi => eq_zero_of_mulVec_sgnOn hv hi
        refine ⟨v 0, v 1, funext fun i => ?_⟩
        fin_cases i <;> simp [hz, hT₂]) hm
  have hc := cent_of_inverts hinv₁ hinv₂
  have hprod := cent_mul (cent_mul (cent_conj hMn hc hz₁X) (cent_conj hMn hc hz₂X))
    (cent_conj hMn hc hz₃X)
  have hword : z₁ * (s₁ * s₂) * z₁⁻¹ * (z₂ * (s₁ * s₂) * z₂⁻¹) * (z₃ * (s₁ * s₂) * z₃⁻¹) = s₁ := by
    rw [hz₁i, hz₂i, hz₃i]
    apply Units.ext
    simp only [Units.val_mul]
    rw [hs₁, hs₂, hz₁, hz₂, hz₃]
    simp only [spMat_mul, mul_assoc]
    exact spMat_congr (by decide) (by decide)
  rw [hword] at hprod
  exact eq_bot_of_inverting hp (by omega) hMp hinv₁ hprod

theorem orth_eq_bot_D6 {Xg Mg : Subgroup (GL (Fin (6 + 1)) (ZMod 3))}
    (hC : ∀ x ∈ Xg, (x : Matrix (Fin (6 + 1)) (Fin (6 + 1)) (ZMod 3)) *ᵥ Pi.single 0 1 =
      Pi.single 0 1 → (x : Matrix (Fin (6 + 1)) (Fin (6 + 1)) (ZMod 3)) ∈ monoFix0 6)
    (hW : ∀ A ∈ evenFix0 6, ∃ x ∈ Xg, (x : Matrix (Fin (6 + 1)) (Fin (6 + 1)) (ZMod 3)) = A)
    (hMX : Mg ≤ Xg) (hMn : ∀ g ∈ Xg, ∀ m ∈ Mg, g * m * g⁻¹ ∈ Mg)
    (hMc : ∀ a ∈ Mg, ∀ b ∈ Mg, a * b = b * a)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hMp : ∀ m ∈ Mg, m ^ p = 1) : Mg = ⊥ := by
  set T₁ : Finset (Fin (6 + 1)) := {1, 2, 3, 4, 5, 6} with hT₁
  set T₂ : Finset (Fin (6 + 1)) := {1, 2, 3, 4} with hT₂
  obtain ⟨s₁, hs₁X, hs₁⟩ := hW _ (sgnOn_mem_evenFix0 T₁ (by decide) (by decide))
  have hσ₂ : spMat (Equiv.swap 5 6) (sgnOn T₂) ∈ evenFix0 6 :=
    ⟨Equiv.swap 5 6, sgnOn T₂, isSign_sgnOn T₂,
      ⟨by decide, by decide, by rw [prod_succ_sgnOn T₂ (by decide)]; decide⟩, rfl⟩
  obtain ⟨s₂, hs₂X, hs₂⟩ := hW _ hσ₂
  obtain ⟨y, hyX, hy⟩ := hW _ (sgnOn_mem_evenFix0 ({1, 5} : Finset (Fin (6 + 1))) (by decide)
    (by decide))
  obtain ⟨z₁, hz₁X, hz₁⟩ := hW _ (perm_mem_evenFix0 (Equiv.swap 1 5 * Equiv.swap 2 6) (by decide))
  obtain ⟨z₂, hz₂X, hz₂⟩ := hW _ (perm_mem_evenFix0 (Equiv.swap 3 5 * Equiv.swap 4 6) (by decide))
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right (gl_mul_self hy (by decide) (by decide))
  have hz₁i : z₁⁻¹ = z₁ := inv_eq_of_mul_eq_one_right (gl_mul_self hz₁ (by decide) (by decide))
  have hz₂i : z₂⁻¹ = z₂ := inv_eq_of_mul_eq_one_right (gl_mul_self hz₂ (by decide) (by decide))
  have hinv₁ : ∀ m ∈ Mg, s₁ * m * s₁⁻¹ = m⁻¹ := fun m hm =>
    orth_inverts (n := 6) (by norm_num) hC hW hMX hMn hMc hp hp5 hMp hs₁X
      (gl_mul_self hs₁ (by decide) (by decide)) (by rw [hs₁]; exact spMat_mulVec_e0 rfl rfl)
      (w := 0) (fun v hv => by
        rw [hs₁] at hv
        have hz : ∀ i ∈ T₁, v i = 0 := fun i hi => eq_zero_of_mulVec_sgnOn hv hi
        refine ⟨v 0, 0, funext fun i => ?_⟩
        fin_cases i <;> simp [hz, hT₁]) hm
  have hinv₂ : ∀ m ∈ Mg, s₂ * m * s₂⁻¹ = m⁻¹ := fun m hm =>
    orth_inverts (n := 6) (by norm_num) hC hW hMX hMn hMc hp hp5 hMp hs₂X
      (gl_mul_self hs₂ (by decide) (by decide))
      (by rw [hs₂]; exact spMat_mulVec_e0 (by decide) (by decide))
      (w := Pi.single 5 1 + Pi.single 6 1) (fun v hv => by
        rw [hs₂] at hv
        obtain ⟨hz, h56⟩ := mulVec_swap_sgnOn (T := T₂) (by decide) (by decide) hv
        refine ⟨v 0, v 5, funext fun i => ?_⟩
        fin_cases i <;> simp [hz, hT₂, h56]) hm
  have hc := cent_of_inverts hinv₁ hinv₂
  have hu := cent_mul hc (cent_conj hMn hc hyX)
  have hprod := cent_mul (cent_mul (cent_conj hMn hu hz₁X) (cent_conj hMn hu hz₂X)) hu
  have hword : z₁ * (s₁ * s₂ * (y * (s₁ * s₂) * y⁻¹)) * z₁⁻¹ *
      (z₂ * (s₁ * s₂ * (y * (s₁ * s₂) * y⁻¹)) * z₂⁻¹) * (s₁ * s₂ * (y * (s₁ * s₂) * y⁻¹)) =
      s₁ := by
    rw [hyi, hz₁i, hz₂i]
    apply Units.ext
    simp only [Units.val_mul]
    rw [hs₁, hs₂, hy, hz₁, hz₂]
    simp only [spMat_mul, mul_assoc]
    exact spMat_congr (by decide) (by decide)
  rw [hword] at hprod
  exact eq_bot_of_inverting hp (by omega) hMp hinv₁ hprod

end CFSG.StandardType.FrameRoute.FS81

end
