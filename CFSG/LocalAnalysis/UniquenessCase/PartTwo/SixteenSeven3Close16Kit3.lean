module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16Kit2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem close16PtStab_of_eq {W : Type} [CommGroup W] {H : Subgroup (MulAut W)} {w a : W}
    (heq : H ⊓ MulAction.stabilizer (MulAut W) w = H ⊓ MulAction.stabilizer (MulAut W) a)
    (h : Close16PtStab H a) : Close16PtStab H w := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [heq]
  exacts [h.maximal, h.card, h.opp, h.quot]

theorem close16_pt_stab_of_two_summands {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    (hH : Nat.card H = 20160) {I : Fin 2 → Subgroup W}
    (hnat : ∀ i, BinaryNaturalSL H (I i) ⊥ 4 1) (hdisj : I 0 ⊓ I 1 = ⊥) (hsup : I 0 ⊔ I 1 = ⊤)
    {τ : MulAut W} (hτ1 : τ ≠ 1) (hτH : ∀ h ∈ H, τ * h = h * τ) {w : W} (hw1 : w ≠ 1)
    (hτw : τ w = w) : Close16PtStab H w := by
  have hinv : ∀ i, ∀ h ∈ H, ∀ x ∈ I i, h x ∈ I i := fun i h hh x hx => by
    obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod (hnat i)
    exact hπ.2.2.2.1 ⟨h, hh⟩ x hx
  have hcomm : ∀ h ∈ H, ∀ x : W, τ (h x) = h (τ x) := fun h hh x => by
    have := congrArg (fun f : MulAut W => f x) (hτH h hh)
    simpa using this
  have hdich : ∀ i, (∀ x ∈ I i, τ x = x) ∨ (∀ x ∈ I i, τ x = x → x = 1) := by
    intro i
    by_cases hex : ∃ u ∈ I i, u ≠ 1 ∧ τ u = u
    · left
      obtain ⟨u, hu, hu1, hτu⟩ := hex
      intro x hx
      by_cases hx1 : x = 1
      · rw [hx1, map_one]
      · obtain ⟨h, hh, hhu⟩ := close16_natural_transitive (hnat i) hu hx hu1 hx1
        rw [← hhu, hcomm h hh, hτu]
    · right
      intro x hx hτx
      by_contra hx1
      exact hex ⟨x, hx, hx1, hτx⟩
  have key : ∀ A B : Subgroup W, A ⊓ B = ⊥ → A ⊔ B = ⊤ → (∀ h ∈ H, ∀ x ∈ A, h x ∈ A) →
      (∀ h ∈ H, ∀ x ∈ B, h x ∈ B) → BinaryNaturalSL H A ⊥ 4 1 →
      (∀ x ∈ B, τ x = x → x = 1) → Close16PtStab H w := by
    intro A B hAB hAB' hA hB hnatA hBfix
    have hw : w ∈ A ⊔ B := by rw [hAB']; exact Subgroup.mem_top w
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup.mp hw
    have hτab : τ a * τ b = a * b := by rw [← map_mul, hab]; exact hτw
    have ha1 : a ≠ 1 := by
      intro ha1
      apply hw1
      rw [← hab, ha1, one_mul]
      refine hBfix b hb ?_
      rwa [ha1, map_one, one_mul, one_mul] at hτab
    have hunique : ∀ a₁ ∈ A, ∀ a₂ ∈ A, ∀ b₁ ∈ B, ∀ b₂ ∈ B, a₁ * b₁ = a₂ * b₂ → a₁ = a₂ := by
      intro a₁ h₁ a₂ h₂ b₁ k₁ b₂ k₂ h
      have hmem : a₁ * a₂⁻¹ ∈ A ⊓ B := by
        refine ⟨A.mul_mem h₁ (A.inv_mem h₂), ?_⟩
        have : a₁ * a₂⁻¹ = b₂ * b₁⁻¹ := by
          rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul, h, mul_comm]
        rw [this]
        exact B.mul_mem k₂ (B.inv_mem k₁)
      rw [hAB, Subgroup.mem_bot, mul_inv_eq_one] at hmem
      exact hmem
    have hstab : ∀ h ∈ H, h w = w ↔ h a = a := by
      intro h hh
      constructor
      · intro hhw
        refine hunique (h a) (hA h hh a ha) a ha (h b) (hB h hh b hb) b hb ?_
        rw [← map_mul, hab, hhw]
      · intro hha
        have hw' : h w = a * h b := by rw [← hab, map_mul, hha]
        have hy : h w * w⁻¹ = h b * b⁻¹ := by
          rw [hw', ← hab, mul_inv_rev]
          calc a * h b * (b⁻¹ * a⁻¹) = h b * b⁻¹ * (a * a⁻¹) := by ac_rfl
            _ = h b * b⁻¹ := by rw [mul_inv_cancel, mul_one]
        have hyB : h w * w⁻¹ ∈ B := by
          rw [hy]
          exact B.mul_mem (hB h hh b hb) (B.inv_mem hb)
        have hyτ : τ (h w * w⁻¹) = h w * w⁻¹ := by
          rw [map_mul, map_inv, hcomm h hh w, hτw]
        have h1 := hBfix _ hyB hyτ
        rwa [mul_inv_eq_one] at h1
    have heq : H ⊓ MulAction.stabilizer (MulAut W) w = H ⊓ MulAction.stabilizer (MulAut W) a := by
      ext h
      simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAut.smul_def]
      constructor
      · rintro ⟨hh, hhw⟩
        exact ⟨hh, (hstab h hh).1 hhw⟩
      · rintro ⟨hh, hha⟩
        exact ⟨hh, (hstab h hh).2 hha⟩
    exact close16PtStab_of_eq heq (close16_natural_stab hH hnatA ha ha1)
  rcases hdich 0 with h0 | h0
  · rcases hdich 1 with h1 | h1
    · exfalso
      refine hτ1 (MulEquiv.ext fun x => ?_)
      have hx : x ∈ I 0 ⊔ I 1 := by rw [hsup]; exact Subgroup.mem_top x
      obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hx
      rw [map_mul, h0 a ha, h1 b hb]
      rfl
    · exact key (I 0) (I 1) hdisj hsup (hinv 0) (hinv 1) (hnat 0) h1
  · exact key (I 1) (I 0) (by rw [inf_comm]; exact hdisj) (by rw [sup_comm]; exact hsup)
      (hinv 1) (hinv 0) (hnat 1) h0

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
