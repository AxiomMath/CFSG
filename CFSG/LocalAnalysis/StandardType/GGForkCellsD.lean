module

public import CFSG.LocalAnalysis.StandardType.GGForkCellsDSpin

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggD4_swap (j : Fin 4) (hj : j = 0 ∨ j = 2 ∨ j = 3) :
    ∀ i j' : Fin 4, CartanMatrix.D 4 (Equiv.swap (0 : Fin 4) j i)
      (Equiv.swap (0 : Fin 4) j j') = CartanMatrix.D 4 i j' := by
  rcases hj with h | h | h <;> subst h <;> intro i j' <;>
    fin_cases i <;> fin_cases j' <;> decide +kernel

private theorem ggD8_swap :
    ∀ i j' : Fin 8, CartanMatrix.D 8 (Equiv.swap (6 : Fin 8) 7 i)
      (Equiv.swap (6 : Fin 8) 7 j') = CartanMatrix.D 8 i j' := by
  intro i j'
  fin_cases i <;> fin_cases j' <;> decide +kernel

theorem ggForkShapeBCD_D4 {Λ : Type} {C : Matrix Λ Λ ℤ} {b : Λ} (e : Fin 4 ≃ Λ)
    (hC : ∀ i j, C (e i) (e j) = CartanMatrix.D 4 i j) (hb : b = e 0 ∨ b = e 2 ∨ b = e 3) :
    GGForkShapeBCD C b := by
  rcases hb with hb | hb | hb
  · exact ⟨1, e, hb.symm, Or.inr (Or.inr ⟨le_rfl, hC⟩)⟩
  · refine ⟨1, (Equiv.swap (0 : Fin 4) 2).trans e, ?_, Or.inr (Or.inr ⟨le_rfl, ?_⟩)⟩
    · simp only [Equiv.trans_apply, Equiv.swap_apply_left]
      exact hb.symm
    · intro i j'
      simp only [Equiv.trans_apply]
      rw [hC]
      exact ggD4_swap 2 (Or.inr (Or.inl rfl)) i j'
  · refine ⟨1, (Equiv.swap (0 : Fin 4) 3).trans e, ?_, Or.inr (Or.inr ⟨le_rfl, ?_⟩)⟩
    · simp only [Equiv.trans_apply, Equiv.swap_apply_left]
      exact hb.symm
    · intro i j'
      simp only [Equiv.trans_apply]
      rw [hC]
      exact ggD4_swap 3 (Or.inr (Or.inr rfl)) i j'

theorem ggForkAffineCell_D8 {Λ : Type} {C : Matrix Λ Λ ℤ} {b : Λ} (e : Fin 8 ≃ Λ)
    (hC : ∀ i j, C (e i) (e j) = CartanMatrix.D 8 i j) (hb : b = e 6 ∨ b = e 7) :
    GGForkAffineCell C b := by
  rcases hb with hb | hb
  · refine Or.inr (Or.inr (Or.inr (Or.inl
      ⟨(Equiv.swap (6 : Fin 8) 7).trans e, ?_, ?_⟩)))
    · intro i j'
      simp only [Equiv.trans_apply]
      rw [hC]
      exact ggD8_swap i j'
    · simp only [Equiv.trans_apply, Equiv.swap_apply_right]
      exact hb
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e, hC, hb⟩)))

theorem ggForkCell_D {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {b c : Λ} (n : ℕ)
    (hn : 1 ≤ n) (e : Fin (n + 3) ≃ Λ)
    (hC : ∀ i j, C (e i) (e j) = CartanMatrix.D (n + 3) i j) (hF : GGForkMatrix C b c) :
    GGForkShapeBCD C b ∨
      (¬ GGAttachNullPos C c ∧ (¬ GGAttachNullPos C b ∨ GGForkAffineCell C b)) := by
  have hleaf : GGLeafPos (CartanMatrix.D (n + 3)) (e.symm b) (e.symm c) := hF.leafPos e hC
  rcases eq_or_lt_of_le hn with h1 | h2
  · have hn1 : n = 1 := h1.symm
    subst hn1
    left
    obtain ⟨-, hb0⟩ := ggLeafPos_D4 hleaf
    have hb : b = e 0 ∨ b = e 2 ∨ b = e 3 := by
      have h0 : b = e (e.symm b) := (Equiv.apply_symm_apply e b).symm
      rcases hb0 with hb0 | hb0 | hb0
      · left; rw [hb0] at h0; exact h0
      · right; left; rw [hb0] at h0; exact h0
      · right; right; rw [hb0] at h0; exact h0
    exact ggForkShapeBCD_D4 e hC hb
  · have hn2 : 2 ≤ n := by omega
    obtain ⟨m, hm⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    subst hm
    obtain ⟨hi0, -⟩ | ⟨hsp, hk⟩ := ggLeafPos_D m hleaf
    · left
      have hi : e.symm b = 0 := Fin.ext hi0
      have heb : e 0 = b := by rw [← hi, Equiv.apply_symm_apply]
      exact ⟨m + 2, e, heb, Or.inr (Or.inr ⟨by omega, hC⟩)⟩
    · right
      constructor
      · have hkc : e.symm c = ⟨m + 2, by omega⟩ := Fin.ext hk
        have hce : c = e ⟨m + 2, by omega⟩ := by rw [← hkc, Equiv.apply_symm_apply]
        exact fun h => ggNoNullPos_D_center m (GGAttachNullPos.of_equiv e hC hce h)
      · by_cases hm3 : m = 3
        · right
          subst hm3
          have hbs : e.symm b = 6 ∨ e.symm b = 7 := by
            rcases hsp with hsp | hsp
            · left; exact Fin.ext hsp
            · right; exact Fin.ext hsp
          have hb8 : b = e 6 ∨ b = e 7 := by
            have h0 : b = e (e.symm b) := (Equiv.apply_symm_apply e b).symm
            rcases hbs with hbs | hbs
            · left; rw [hbs] at h0; exact h0
            · right; rw [hbs] at h0; exact h0
          exact ggForkAffineCell_D8 e hC hb8
        · left
          have h0 : b = e (e.symm b) := (Equiv.apply_symm_apply e b).symm
          exact fun h =>
            ggNoNullPos_D_spin m hm3 hsp (GGAttachNullPos.of_equiv e hC h0 h)

end CFSG.StandardType
