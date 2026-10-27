module

public import CFSG.RankThree.PartTwo.Sec21.FF81GL6B3

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.GL6

open Matrix

private theorem na_mulVec_mul (A B : G6) (v : Fin 6 → ZMod 2) :
    ((A * B : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v =
      (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ ((B : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v) := by
  rw [Units.val_mul, Matrix.mulVec_mulVec]

private theorem na_inv_mulVec (g : G6) (v : Fin 6 → ZMod 2) :
    ((g⁻¹ : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
      ((g : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

private theorem na_mulVec_inv (g : G6) (v : Fin 6 → ZMod 2) :
    (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
      (((g⁻¹ : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem card_fix_conj (σ b : G6) :
    Nat.card {v : Fin 6 → ZMod 2 //
        ((σ * b * σ⁻¹ : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v = v} =
      Nat.card {v : Fin 6 → ZMod 2 // (b : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v = v} := by
  have e : ∀ w : Fin 6 → ZMod 2,
      ((σ * b * σ⁻¹ : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ w =
        (σ : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
          ((b : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
            (((σ⁻¹ : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ w)) := by
    intro w
    rw [na_mulVec_mul, na_mulVec_mul]
  let f : (Fin 6 → ZMod 2) ≃ (Fin 6 → ZMod 2) :=
    { toFun := fun w => ((σ⁻¹ : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ w
      invFun := fun w => (σ : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ w
      left_inv := fun w => na_mulVec_inv σ w
      right_inv := fun w => na_inv_mulVec σ w }
  refine Nat.card_congr (Equiv.subtypeEquiv f fun v => ?_)
  show _ ↔ (b : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
    (((σ⁻¹ : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v) =
      ((σ⁻¹ : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v
  constructor
  · intro h
    have h' : (σ : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
        ((b : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
          (((σ⁻¹ : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v)) = v :=
      (e v).symm.trans h
    calc (b : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
          (((σ⁻¹ : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v)
        = ((σ⁻¹ : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
            ((σ : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
              ((b : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ
                (((σ⁻¹ : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v))) :=
          (na_inv_mulVec σ _).symm
      _ = ((σ⁻¹ : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v := by rw [h']
  · intro h
    show ((σ * b * σ⁻¹ : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v = v
    rw [e v, h]
    exact na_mulVec_inv σ v

private theorem na_card_fix_eq (g : G6) :
    Nat.card {v : Fin 6 → ZMod 2 // (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v = v} =
      (Finset.univ.filter fun v : Fin 6 → ZMod 2 =>
        (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v = v).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

def uu : Fin 3 → G6 := ![u2, u3, u0]

private theorem na_uu_zero : uu 0 = u2 := rfl

private theorem na_uu_one : uu 1 = u3 := rfl

private theorem na_uu_two : uu 2 = u0 := rfl

private theorem na_fix_table : ∀ a b c : Fin 3,
    (Finset.univ.filter fun v : Fin 6 → ZMod 2 =>
      ((u0 ^ (a : ℕ) * u2 ^ (b : ℕ) * u3 ^ (c : ℕ) : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v
        = v).card =
      (if (a : ℕ) = 0 then 4 else 1) * (if (b : ℕ) = 0 then 4 else 1) *
        (if (c : ℕ) = 0 then 4 else 1) := by
  decide +kernel

private theorem na_uu_table : ∀ i : Fin 3,
    (Finset.univ.filter fun v : Fin 6 → ZMod 2 =>
      ((uu i : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v = v).card = 16 := by
  decide +kernel

private theorem na_card_fix_uu (i : Fin 3) :
    Nat.card {v : Fin 6 → ZMod 2 //
      ((uu i : G6) : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v = v} = 16 :=
  (na_card_fix_eq (uu i)).trans (na_uu_table i)

private theorem na_fix_cases : ∀ a b c : Fin 3,
    (if (a : ℕ) = 0 then 4 else 1) * (if (b : ℕ) = 0 then 4 else 1) *
        (if (c : ℕ) = 0 then 4 else 1) = 16 →
      ((a : ℕ) ≠ 0 ∧ (b : ℕ) = 0 ∧ (c : ℕ) = 0) ∨ ((a : ℕ) = 0 ∧ (b : ℕ) ≠ 0 ∧ (c : ℕ) = 0) ∨
        ((a : ℕ) = 0 ∧ (b : ℕ) = 0 ∧ (c : ℕ) ≠ 0) := by
  decide

theorem uu_mem_B3 (i : Fin 3) : uu i ∈ B3 := by
  have h0 : u0 ∈ B3 := Subgroup.subset_closure (by simp)
  have h2 : u2 ∈ B3 := Subgroup.subset_closure (by simp)
  have h3 : u3 ∈ B3 := Subgroup.subset_closure (by simp)
  fin_cases i
  · exact h2
  · exact h3
  · exact h0

theorem special_of_card_fix {g : G6} (hg : g ∈ B3)
    (h : Nat.card {v : Fin 6 → ZMod 2 // (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v = v} = 16) :
    ∃ (j : Fin 3) (k : ℕ), (k = 1 ∨ k = 2) ∧ g = uu j ^ k := by
  obtain ⟨a, b, c, rfl⟩ := mem_B3_iff.1 hg
  rw [na_card_fix_eq, na_fix_table a b c] at h
  rcases na_fix_cases a b c h with ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩
  · refine ⟨2, (a : ℕ), ?_, ?_⟩
    · have := a.isLt
      omega
    · simp [hb, hc, na_uu_two]
  · refine ⟨0, (b : ℕ), ?_, ?_⟩
    · have := b.isLt
      omega
    · simp [ha, hc, na_uu_zero]
  · refine ⟨1, (c : ℕ), ?_, ?_⟩
    · have := c.isLt
      omega
    · simp [ha, hb, na_uu_one]

theorem normalizer_special {σ : G6} (hσ : σ ∈ Subgroup.normalizer (B3 : Set G6)) (i : Fin 3) :
    ∃ (j : Fin 3) (k : ℕ), (k = 1 ∨ k = 2) ∧ σ * uu i * σ⁻¹ = uu j ^ k := by
  have hmem : σ * uu i * σ⁻¹ ∈ B3 :=
    (Subgroup.mem_set_normalizer_iff.1 hσ (uu i)).1 (uu_mem_B3 i)
  exact special_of_card_fix hmem ((card_fix_conj σ (uu i)).trans (na_card_fix_uu i))

end CFSG.RankThree.PartTwo.Sec21.FF81.GL6
