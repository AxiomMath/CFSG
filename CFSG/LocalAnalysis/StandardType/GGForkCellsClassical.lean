module

public import CFSG.LocalAnalysis.StandardType.GGForkCellsExceptional

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem eq_of_neg_one_eq_ite {m : ℕ} {j k : Fin m}
    (h : (-1 : ℤ) = if j = k then -1 else 0) : j = k := by
  by_contra hne
  rw [if_neg hne] at h
  omega

private theorem ggLeafPos_transpose {m : ℕ} {C₀ : Matrix (Fin m) (Fin m) ℤ} {i k : Fin m} :
    GGLeafPos (Matrix.transpose C₀) i k ↔ GGLeafPos C₀ i k := by
  unfold GGLeafPos
  simp only [Matrix.transpose_apply]
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h1, h3, h2⟩

private theorem A_apply_of_adj (n : ℕ) {i j : Fin n}
    (h : i.val + 1 = j.val ∨ j.val + 1 = i.val) (hne : i ≠ j) :
    CartanMatrix.A n i j = -1 := by
  simp only [CartanMatrix.A, Matrix.of_apply]
  rw [if_neg hne, if_pos h]

private theorem B_apply_of_adj (n : ℕ) {i j : Fin n}
    (h : i.val + 1 = j.val) (hj : j.val ≠ n - 1) (hne : i ≠ j) :
    CartanMatrix.B n i j = -1 := by
  simp only [CartanMatrix.B, Matrix.of_apply]
  rw [if_neg hne, if_pos h, if_neg hj]

private theorem B_apply_of_adj' (n : ℕ) {i j : Fin n}
    (h : j.val + 1 = i.val) (h' : i.val + 1 ≠ j.val) (hne : i ≠ j) :
    CartanMatrix.B n i j = -1 := by
  simp only [CartanMatrix.B, Matrix.of_apply]
  rw [if_neg hne, if_neg h', if_pos h]

private theorem B_apply_of_adj2 (n : ℕ) {i j : Fin n}
    (h : i.val + 1 = j.val) (hj : j.val = n - 1) (hne : i ≠ j) :
    CartanMatrix.B n i j = -2 := by
  simp only [CartanMatrix.B, Matrix.of_apply]
  rw [if_neg hne, if_pos h, if_pos hj]

theorem ggLeafPos_A {n : ℕ} (hn : 2 ≤ n) {i k : Fin n} (h : GGLeafPos (CartanMatrix.A n) i k) :
    (i.val = 0 ∧ k.val = 1) ∨ (i.val + 1 = n ∧ k.val + 2 = n) := by
  obtain ⟨-, hrow, -⟩ := h
  rcases Nat.eq_zero_or_pos i.val with hi0 | hipos
  · left
    have h1n : 1 < n := by omega
    have hji : (⟨1, h1n⟩ : Fin n) ≠ i := by
      intro hh
      have := congrArg Fin.val hh
      simp [hi0] at this
    have hA : CartanMatrix.A n i (⟨1, h1n⟩ : Fin n) = -1 :=
      A_apply_of_adj n (Or.inl (by simp [hi0])) (Ne.symm hji)
    have hk := hrow (⟨1, h1n⟩ : Fin n) hji
    rw [hA] at hk
    have hjk := eq_of_neg_one_eq_ite hk
    refine ⟨hi0, ?_⟩
    rw [← hjk]
  · rcases Nat.lt_or_ge i.val (n - 1) with hlt | hge
    · exfalso
      have h1lt : i.val - 1 < n := by omega
      have h2lt : i.val + 1 < n := by omega
      have hj1i : (⟨i.val - 1, h1lt⟩ : Fin n) ≠ i := by
        intro hh
        have := congrArg Fin.val hh
        simp at this
        omega
      have hj2i : (⟨i.val + 1, h2lt⟩ : Fin n) ≠ i := by
        intro hh
        have := congrArg Fin.val hh
        simp at this
      have hA1 : CartanMatrix.A n i (⟨i.val - 1, h1lt⟩ : Fin n) = -1 :=
        A_apply_of_adj n (Or.inr (by simp; omega)) (Ne.symm hj1i)
      have hA2 : CartanMatrix.A n i (⟨i.val + 1, h2lt⟩ : Fin n) = -1 :=
        A_apply_of_adj n (Or.inl (by simp)) (Ne.symm hj2i)
      have hk1 := hrow (⟨i.val - 1, h1lt⟩ : Fin n) hj1i
      have hk2 := hrow (⟨i.val + 1, h2lt⟩ : Fin n) hj2i
      rw [hA1] at hk1
      rw [hA2] at hk2
      have he1 := eq_of_neg_one_eq_ite hk1
      have he2 := eq_of_neg_one_eq_ite hk2
      have hEq : (⟨i.val - 1, h1lt⟩ : Fin n) = (⟨i.val + 1, h2lt⟩ : Fin n) :=
        he1.trans he2.symm
      have := congrArg Fin.val hEq
      simp at this
    · right
      have hival : i.val = n - 1 := by omega
      have h2lt : n - 2 < n := by omega
      have hji : (⟨n - 2, h2lt⟩ : Fin n) ≠ i := by
        intro hh
        have hh' := congrArg Fin.val hh
        simp at hh'
        omega
      have hA : CartanMatrix.A n i (⟨n - 2, h2lt⟩ : Fin n) = -1 :=
        A_apply_of_adj n (Or.inr (by simp; omega)) (Ne.symm hji)
      have hk := hrow (⟨n - 2, h2lt⟩ : Fin n) hji
      rw [hA] at hk
      have hjk := eq_of_neg_one_eq_ite hk
      refine ⟨by omega, ?_⟩
      rw [← hjk]
      simp only [Fin.val_mk]
      omega

theorem ggLeafPos_B {n : ℕ} (hn : 3 ≤ n) {i k : Fin n} (h : GGLeafPos (CartanMatrix.B n) i k) :
    i.val = 0 ∧ k.val = 1 := by
  obtain ⟨-, hrow, hcol⟩ := h
  have hi0 : i.val = 0 := by
    rcases Nat.eq_zero_or_pos i.val with h0 | hpos
    · exact h0
    · rcases Nat.lt_or_ge i.val (n - 1) with hlt | hge
      · by_cases hmid : i.val + 1 = n - 1
        · exfalso
          have h2lt : i.val + 1 < n := by omega
          have hji : (⟨i.val + 1, h2lt⟩ : Fin n) ≠ i := by
            intro hh
            have := congrArg Fin.val hh
            simp at this
          have hA : CartanMatrix.B n i (⟨i.val + 1, h2lt⟩ : Fin n) = -2 :=
            B_apply_of_adj2 n (by simp) (by simpa using hmid) (Ne.symm hji)
          have hk := hrow (⟨i.val + 1, h2lt⟩ : Fin n) hji
          rw [hA] at hk
          by_cases hjk : (⟨i.val + 1, h2lt⟩ : Fin n) = k
          · rw [if_pos hjk] at hk; omega
          · rw [if_neg hjk] at hk; omega
        · exfalso
          have h1lt : i.val - 1 < n := by omega
          have h2lt : i.val + 1 < n := by omega
          have hj1i : (⟨i.val - 1, h1lt⟩ : Fin n) ≠ i := by
            intro hh
            have := congrArg Fin.val hh
            simp at this
            omega
          have hj2i : (⟨i.val + 1, h2lt⟩ : Fin n) ≠ i := by
            intro hh
            have := congrArg Fin.val hh
            simp at this
          have hA1 : CartanMatrix.B n i (⟨i.val - 1, h1lt⟩ : Fin n) = -1 :=
            B_apply_of_adj' n (by simp; omega) (by simp; omega) (Ne.symm hj1i)
          have hA2 : CartanMatrix.B n i (⟨i.val + 1, h2lt⟩ : Fin n) = -1 :=
            B_apply_of_adj n (by simp) (by simpa using hmid) (Ne.symm hj2i)
          have hk1 := hrow (⟨i.val - 1, h1lt⟩ : Fin n) hj1i
          have hk2 := hrow (⟨i.val + 1, h2lt⟩ : Fin n) hj2i
          rw [hA1] at hk1
          rw [hA2] at hk2
          have he1 := eq_of_neg_one_eq_ite hk1
          have he2 := eq_of_neg_one_eq_ite hk2
          have hEq : (⟨i.val - 1, h1lt⟩ : Fin n) = (⟨i.val + 1, h2lt⟩ : Fin n) :=
            he1.trans he2.symm
          have := congrArg Fin.val hEq
          simp at this
      · exfalso
        have hival : i.val = n - 1 := by omega
        have h2lt : n - 2 < n := by omega
        have hji : (⟨n - 2, h2lt⟩ : Fin n) ≠ i := by
          intro hh
          have hh' := congrArg Fin.val hh
          simp at hh'
          omega
        have hA : CartanMatrix.B n (⟨n - 2, h2lt⟩ : Fin n) i = -2 :=
          B_apply_of_adj2 n (by simp; omega) (by simpa using hival) hji
        have hk := hcol (⟨n - 2, h2lt⟩ : Fin n) hji
        rw [hA] at hk
        by_cases hjk : (⟨n - 2, h2lt⟩ : Fin n) = k
        · rw [if_pos hjk] at hk; omega
        · rw [if_neg hjk] at hk; omega
  · refine ⟨hi0, ?_⟩
    have h1n : 1 < n := by omega
    have hji : (⟨1, h1n⟩ : Fin n) ≠ i := by
      intro hh
      have := congrArg Fin.val hh
      simp [hi0] at this
    have hA : CartanMatrix.B n i (⟨1, h1n⟩ : Fin n) = -1 :=
      B_apply_of_adj n (by simp [hi0]) (by simp; omega) (Ne.symm hji)
    have hk := hrow (⟨1, h1n⟩ : Fin n) hji
    rw [hA] at hk
    have hjk := eq_of_neg_one_eq_ite hk
    rw [← hjk]

theorem ggLeafPos_C {n : ℕ} (hn : 3 ≤ n) {i k : Fin n} (h : GGLeafPos (CartanMatrix.C n) i k) :
    i.val = 0 ∧ k.val = 1 := by
  rw [← CartanMatrix.B_transpose] at h
  exact ggLeafPos_B hn (ggLeafPos_transpose.mp h)

theorem ggLeafPos_B2 : ∀ i k : Fin 2, ¬ GGLeafPos (CartanMatrix.B 2) i k := by
  decide +kernel

theorem ggLeafPos_C2 : ∀ i k : Fin 2, ¬ GGLeafPos (CartanMatrix.C 2) i k := by
  decide +kernel

theorem ggLeafPos_G2 : ∀ i k : Fin 2, ¬ GGLeafPos CartanMatrix.G₂ i k := by
  decide +kernel

theorem ggLeafPos_G2T : ∀ i k : Fin 2, ¬ GGLeafPos (Matrix.transpose CartanMatrix.G₂) i k := by
  decide +kernel

theorem cartanMatrix_A_rev (n : ℕ) (i j : Fin n) :
    CartanMatrix.A n (Fin.rev i) (Fin.rev j) = CartanMatrix.A n i j := by
  by_cases hij : i = j
  · subst hij
    simp [CartanMatrix.A, Matrix.of_apply]
  · have hrev : ¬ (Fin.rev i = Fin.rev j) := fun h => hij (Fin.rev_injective h)
    have harith :
        ((Fin.rev i).val + 1 = (Fin.rev j).val ∨ (Fin.rev j).val + 1 = (Fin.rev i).val) ↔
          (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
      rw [Fin.val_rev, Fin.val_rev]
      constructor
      · rintro (h | h)
        · right; omega
        · left; omega
      · rintro (h | h)
        · right; omega
        · left; omega
    simp only [CartanMatrix.A, Matrix.of_apply]
    rw [if_neg hrev, if_neg hij, if_congr harith rfl rfl]

theorem ggForkCell_A {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {b c : Λ} {n : ℕ}
    (hn : 1 ≤ n) (e : Fin n ≃ Λ) (hC : ∀ i j, C (e i) (e j) = CartanMatrix.A n i j)
    (hF : GGForkMatrix C b c) :
    GGForkShapeA C b ∨
      (¬ GGAttachNullPos C c ∧ (¬ GGAttachNullPos C b ∨ GGForkAffineCell C b)) := by
  rcases n with _ | _ | _ | n
  · exfalso; omega
  · refine False.elim ((hF.leafPos e hC).1 ?_)
    apply Fin.ext
    have hb := (e.symm b).isLt
    have hc := (e.symm c).isLt
    omega
  · exact Or.inr (ggForkCell_A2 e hC hF)
  · rcases ggLeafPos_A (by omega) (hF.leafPos e hC) with ⟨hi0, -⟩ | ⟨hi1, -⟩
    · have hsymm : e.symm b = 0 := Fin.ext (by simpa using hi0)
      have hb : e 0 = b := by rw [← hsymm, e.apply_symm_apply]
      refine Or.inl ⟨n + 2, Fin.revPerm.trans e, by omega, ?_, ?_⟩
      · rw [Equiv.trans_apply, Fin.revPerm_apply, Fin.rev_last]
        exact hb
      · intro i j
        simp only [Equiv.trans_apply, Fin.revPerm_apply]
        exact (hC (Fin.rev i) (Fin.rev j)).trans (cartanMatrix_A_rev _ i j)
    · have hsymm : e.symm b = Fin.last (n + 2) :=
        Fin.ext (by simp only [Fin.val_last]; omega)
      refine Or.inl ⟨n + 2, e, by omega, ?_, hC⟩
      rw [← hsymm, e.apply_symm_apply]

theorem ggForkCell_BC {Λ : Type} [Fintype Λ] [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {b c : Λ} {n : ℕ}
    (hn : 2 ≤ n) (e : Fin n ≃ Λ)
    (hC : (∀ i j, C (e i) (e j) = CartanMatrix.B n i j) ∨
      (∀ i j, C (e i) (e j) = CartanMatrix.C n i j))
    (hF : GGForkMatrix C b c) : GGForkShapeBCD C b := by
  rcases n with _ | _ | _ | n
  · exfalso; omega
  · exfalso; omega
  · exfalso
    rcases hC with hB | hC
    · exact ggLeafPos_B2 _ _ (hF.leafPos e hB)
    · exact ggLeafPos_C2 _ _ (hF.leafPos e hC)
  · rcases hC with hB | hC
    · have h0 := (ggLeafPos_B (by omega) (hF.leafPos e hB)).1
      have hsymm : e.symm b = 0 := Fin.ext (by simpa using h0)
      have hb : e 0 = b := by rw [← hsymm, e.apply_symm_apply]
      exact ⟨n, e, hb, Or.inl hB⟩
    · have h0 := (ggLeafPos_C (by omega) (hF.leafPos e hC)).1
      have hsymm : e.symm b = 0 := Fin.ext (by simpa using h0)
      have hb : e 0 = b := by rw [← hsymm, e.apply_symm_apply]
      exact ⟨n, e, hb, Or.inr (Or.inl hC)⟩

theorem ggForkCell_G2 {Λ : Type} [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {b c : Λ} (e : Fin 2 ≃ Λ)
    (hC : (∀ i j, C (e i) (e j) = CartanMatrix.G₂ i j) ∨
      (∀ i j, C (e i) (e j) = CartanMatrix.G₂ j i))
    (hF : GGForkMatrix C b c) : False := by
  rcases hC with h1 | h2
  · exact ggLeafPos_G2 _ _ (hF.leafPos e h1)
  · refine ggLeafPos_G2T _ _ (hF.leafPos e ?_)
    intro i j
    rw [h2 i j, Matrix.transpose_apply]

end CFSG.StandardType
