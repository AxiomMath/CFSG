module

public import CFSG.Quasithin.Vol2.Ch4Sec2NSBOddLA

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

@[expose] def PresA {n : ℕ} (m : ℕ) (g : Matrix (Fin n) (Fin n) (ZMod 2)) : Prop :=
  ∀ a b : Fin n, a.val < m → m ≤ b.val → g b a = 0

theorem presA_of_fixesA {n m : ℕ} {g : Matrix (Fin n) (Fin n) (ZMod 2)} (h : FixesA m g) :
    PresA m g := by
  intro a b ha hb
  have hne : b ≠ a := by
    intro e
    subst e
    omega
  have h' := congrFun (h a ha) b
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, hne] using h'

theorem lowerBlock2_mul_of_presA {n m : ℕ} (h : n = m + 2)
    {g₁ g₂ : Matrix (Fin n) (Fin n) (ZMod 2)} (h₁ : PresA m g₁) (h₂ : PresA m g₂) :
    lowerBlock2 h (g₁ * g₂) = lowerBlock2 h g₁ * lowerBlock2 h g₂ := by
  subst h
  ext a b
  have ha := a.isLt
  have hb := b.isLt
  simp only [lowerBlock2, Matrix.mul_apply]
  rw [Fin.sum_univ_add]
  have hA : ∀ c : Fin m, g₁ ⟨m + a.val, by omega⟩ (Fin.castAdd 2 c) *
      g₂ (Fin.castAdd 2 c) ⟨m + b.val, by omega⟩ = 0 := by
    intro c
    have hz := h₁ (Fin.castAdd 2 c) ⟨m + a.val, by omega⟩ (by simpa using c.isLt)
      (Nat.le_add_right _ _)
    rw [hz, zero_mul]
  rw [Finset.sum_eq_zero (fun c _ => hA c), zero_add]
  exact Finset.sum_congr rfl (fun k _ => rfl)

private theorem transvection_mulVec_nsbg {m : ℕ} (i j : Fin m) (w : Fin m → ZMod 2) :
    (Matrix.transvection i j (1 : ZMod 2)).mulVec w = w + Pi.single i (w j) := by
  funext l
  simp [Matrix.transvection, Matrix.add_mulVec, Matrix.single_mulVec, Pi.single_apply,
    Function.update_apply]

theorem exists_gl_lower_transvection {n m : ℕ} (h : n = m + 2) :
    ∃ g : GL (Fin n) (ZMod 2), FixesA m (g : Matrix (Fin n) (Fin n) (ZMod 2)) ∧
      lowerBlock2 h (g : Matrix (Fin n) (Fin n) (ZMod 2)) ≠ 1 ∧
      lowerBlock2 h (g : Matrix (Fin n) (Fin n) (ZMod 2)) *
        lowerBlock2 h (g : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
  obtain ⟨i, hi⟩ : ∃ i : Fin n, i.val = m := ⟨⟨m, by omega⟩, rfl⟩
  obtain ⟨j, hj⟩ : ∃ j : Fin n, j.val = m + 1 := ⟨⟨m + 1, by omega⟩, rfl⟩
  have hij : i ≠ j := by
    intro e
    have := congrArg Fin.val e
    omega
  have hdet : IsUnit (Matrix.transvection i j (1 : ZMod 2)).det := by
    rw [Matrix.det_transvection_of_ne i j hij 1]
    exact isUnit_one
  obtain ⟨g, hgT⟩ : ∃ g : GL (Fin n) (ZMod 2),
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) = Matrix.transvection i j (1 : ZMod 2) :=
    ⟨Matrix.GeneralLinearGroup.mk'' _ hdet, rfl⟩
  have hfix : FixesA m (Matrix.transvection i j (1 : ZMod 2)) := by
    intro a ha
    rw [transvection_mulVec_nsbg]
    have hne : j ≠ a := by
      intro e
      have := congrArg Fin.val e
      omega
    rw [Pi.single_apply, if_neg hne, Pi.single_zero, add_zero]
  have hTT : Matrix.transvection i j (1 : ZMod 2) * Matrix.transvection i j (1 : ZMod 2) = 1 := by
    rw [Matrix.transvection_mul_transvection_same i j hij,
      show (1 : ZMod 2) + 1 = 0 by decide, Matrix.transvection_zero]
  have hpre : PresA m (Matrix.transvection i j (1 : ZMod 2)) := presA_of_fixesA hfix
  have hentry : (Matrix.transvection i j (1 : ZMod 2)) i j = 1 := by
    rw [Matrix.transvection, Matrix.add_apply, Matrix.one_apply_ne hij, zero_add,
      Matrix.single_apply_same]
  have hblock01 : lowerBlock2 h (Matrix.transvection i j (1 : ZMod 2)) 0 1 = 1 := by
    have e1 : (⟨m + (0 : Fin 2).val, by omega⟩ : Fin n) = i := Fin.ext (by simp [hi])
    have e2 : (⟨m + (1 : Fin 2).val, by omega⟩ : Fin n) = j := Fin.ext (by simp [hj])
    show Matrix.transvection i j (1 : ZMod 2) ⟨m + (0 : Fin 2).val, by omega⟩
      ⟨m + (1 : Fin 2).val, by omega⟩ = 1
    rw [e1, e2, hentry]
  refine ⟨g, ?_, ?_, ?_⟩
  · rw [hgT]
    exact hfix
  · rw [hgT]
    intro e
    have h01 := congrFun (congrFun e 0) 1
    rw [hblock01, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide)] at h01
    exact one_ne_zero h01
  · rw [hgT, ← lowerBlock2_mul_of_presA h hpre hpre, hTT, lowerBlock2_one h]

end CFSG.Quasithin.H13.Ch4.NSB
