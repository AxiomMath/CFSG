module

public import CFSG.Quasithin.Vol2.Ch11SecOE8L

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

namespace L3T

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour CFSG.QuasithinUnique.Fin257
  CFSG.QuasithinUnique.Fin257.L3

variable {F : Type} [Field F] [CharP F 2]

theorem eq_of_card_four [Finite F] (hF : Nat.card F = 4) {c₀ c₁ : F} (h0 : c₀ ≠ 0) (h1 : c₁ ≠ 0)
    (h01 : c₁ ≠ c₀) (d : F) : d = 0 ∨ d = c₀ ∨ d = c₁ ∨ d = c₀ + c₁ := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hs : ({0, c₀, c₁, c₀ + c₁} : Finset F) = Finset.univ := by
    apply Finset.eq_univ_of_card
    have e1 : c₀ + c₁ ≠ 0 := fun h => h01 (by
      linear_combination h - c₀ * (CharTwo.two_eq_zero : (2 : F) = 0))
    have e2 : c₀ + c₁ ≠ c₀ := fun h => h1 (by linear_combination h)
    have e3 : c₀ + c₁ ≠ c₁ := fun h => h0 (by linear_combination h)
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair e3.symm]
    · rw [← Nat.card_eq_fintype_card, hF]
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h01.symm, e2.symm⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨h0.symm, h1.symm, e1.symm⟩
  have hd : d ∈ ({0, c₀, c₁, c₀ + c₁} : Finset F) := by rw [hs]; exact Finset.mem_univ d
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hd

theorem fix_Wg_of_card_four [Finite F] (hF : Nat.card F = 4) {B : Subgroup (projectiveSL 3 F)}
    (hBW : B ≤ (Wg : Subgroup (projectiveSL 3 F))) (hB2 : Nat.card B = 2)
    {θ₁ θ₂ : MulAut (projectiveSL 3 F)}
    (h₁U : ∀ u ∈ projUnitriangular 3 F, θ₁ u ∈ projUnitriangular 3 F)
    (h₂U : ∀ u ∈ projUnitriangular 3 F, θ₂ u ∈ projUnitriangular 3 F)
    (h₁B : ∀ g ∈ B, θ₁ g = g) (h₂B : ∀ g ∈ B, θ₂ g = g)
    (h₁ : ¬ ∀ g ∈ (Wg : Subgroup (projectiveSL 3 F)), θ₁ g = g) :
    (∀ g ∈ (Wg : Subgroup (projectiveSL 3 F)), θ₂ g = g) ∨
      ∀ g ∈ (Wg : Subgroup (projectiveSL 3 F)), (θ₁ * θ₂) g = g := by
  classical
  obtain ⟨⟨z, hzB⟩, hz1⟩ : ∃ x : B, x ≠ 1 := by
    by_contra h
    push Not at h
    have : Nat.card B = 1 := Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => (h a).trans (h b).symm⟩,
      ⟨1⟩⟩
    omega
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  obtain ⟨c₀, rfl⟩ := mem_Wg.mp (hBW hzB)
  have hc₀ : c₀ ≠ 0 := fun h => hz1' (by rw [h, wP_zero])
  obtain ⟨c₁, hc₁0, hc₁⟩ : ∃ c₁ : F, c₁ ≠ 0 ∧ c₁ ≠ c₀ := by
    by_contra h
    push Not at h
    have : Fintype F := Fintype.ofFinite F
    have hsub : (Finset.univ : Finset F) ⊆ {0, c₀} := fun d _ => by
      by_cases hd : d = 0
      · simp [hd]
      · simp [h d hd]
    have := Finset.card_le_card hsub
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hF] at this
    have h2 := Finset.card_le_two (a := (0 : F)) (b := c₀)
    omega
  have himg : ∀ α : MulAut (projectiveSL 3 F),
      (∀ u ∈ projUnitriangular 3 F, α u ∈ projUnitriangular 3 F) → α (wP c₀) = wP c₀ →
        α (wP c₁) = wP c₁ ∨ α (wP c₁) = wP c₀ * wP c₁ := by
    intro α hαU hαz
    have hmem : α (wP c₁) ∈ (Wg : Subgroup (projectiveSL 3 F)) := by
      rw [← map_Wg hαU]
      exact ⟨wP c₁, ⟨c₁, rfl⟩, rfl⟩
    obtain ⟨d, hd⟩ := mem_Wg.mp hmem
    rcases eq_of_card_four hF hc₀ hc₁0 hc₁ d with h | h | h | h
    · exfalso
      rw [h, wP_zero, ← map_one α] at hd
      exact hc₁0 ((wP_eq_one_iff _).mp (α.injective hd))
    · exfalso
      rw [h, ← hαz] at hd
      exact hc₁ (wP_injective (α.injective hd))
    · exact Or.inl (hd.trans (by rw [h]))
    · exact Or.inr (hd.trans (by rw [h, wP_add]))
  have hfixW : ∀ α : MulAut (projectiveSL 3 F), α (wP c₀) = wP c₀ → α (wP c₁) = wP c₁ →
      ∀ g ∈ (Wg : Subgroup (projectiveSL 3 F)), α g = g := by
    intro α h0 h1 g hg
    obtain ⟨d, rfl⟩ := mem_Wg.mp hg
    rcases eq_of_card_four hF hc₀ hc₁0 hc₁ d with h | h | h | h
    · rw [h, wP_zero, map_one]
    · rw [h, h0]
    · rw [h, h1]
    · rw [h, wP_add, map_mul, h0, h1]
  have hz₁ : θ₁ (wP c₀) = wP c₀ := h₁B _ hzB
  have hz₂ : θ₂ (wP c₀) = wP c₀ := h₂B _ hzB
  have hy₁ : θ₁ (wP c₁) = wP c₀ * wP c₁ := by
    rcases himg θ₁ h₁U hz₁ with h | h
    · exact absurd (hfixW θ₁ hz₁ h) h₁
    · exact h
  rcases himg θ₂ h₂U hz₂ with h | h
  · exact Or.inl (hfixW θ₂ hz₂ h)
  · refine Or.inr (hfixW _ ?_ ?_)
    · rw [MulAut.mul_apply, hz₂, hz₁]
    · rw [MulAut.mul_apply, h, map_mul, hz₁, hy₁, ← mul_assoc, wP_mul_self, one_mul]

end L3T

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
