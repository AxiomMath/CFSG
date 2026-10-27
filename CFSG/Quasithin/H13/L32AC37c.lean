module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits Matrix

theorem exists_dotProduct_of_ne {n : ℕ} {w₂ w : Fin n → ZMod 2} (hw : w ≠ 0) (hww : w ≠ w₂) :
    ∃ ψ : Fin n → ZMod 2, ψ ⬝ᵥ w₂ = 0 ∧ ψ ⬝ᵥ w = 1 := by
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  by_cases h : ∃ i, w i = 1 ∧ w₂ i = 0
  · obtain ⟨i, hi, hi'⟩ := h
    exact ⟨Pi.single i 1, by rw [single_one_dotProduct, hi'], by rw [single_one_dotProduct, hi]⟩
  · push Not at h
    obtain ⟨i, hi⟩ : ∃ i, w i = 1 := by
      by_contra h'
      push Not at h'
      exact hw (funext fun i => (h01 (w i)).resolve_right (h' i))
    obtain ⟨j, hj⟩ : ∃ j, w j ≠ w₂ j := by
      by_contra h'
      push Not at h'
      exact hww (funext h')
    have hi' : w₂ i = 1 := (h01 _).resolve_left (h i hi)
    have hj0 : w j = 0 := (h01 _).resolve_right fun h1 =>
      hj (h1.trans ((h01 _).resolve_left (h j h1)).symm)
    have hj1 : w₂ j = 1 := (h01 _).resolve_left fun h2 => hj (hj0.trans h2.symm)
    refine ⟨Pi.single i 1 + Pi.single j 1, ?_, ?_⟩
    · rw [add_dotProduct, single_one_dotProduct, single_one_dotProduct, hi', hj1]
      decide
    · rw [add_dotProduct, single_one_dotProduct, single_one_dotProduct, hi, hj0, add_zero]

theorem exists_sl_fix_of_ne {n : ℕ} {w₂ w : Fin n → ZMod 2} (hw : w ≠ 0) (hww : w ≠ w₂)
    (c : Fin n → ZMod 2) : ∃ g : SpecialLinearGroup (Fin n) (ZMod 2),
      (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ w₂ = w₂ ∧
      ((g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ w = c ∨
        (g : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ w = w + c) := by
  obtain ⟨ψ, h2, h1⟩ := exists_dotProduct_of_ne hw hww
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have hcw : w + (c + w) = c := by
    funext i
    simp only [Pi.add_apply]
    generalize w i = p
    generalize c i = q
    revert p q
    decide
  obtain ⟨d, hd, hwd⟩ : ∃ d : Fin n → ZMod 2, ψ ⬝ᵥ d = 0 ∧ (w + d = c ∨ w + d = w + c) := by
    rcases h01 (ψ ⬝ᵥ c) with h | h
    · exact ⟨c, h, Or.inr rfl⟩
    · refine ⟨c + w, ?_, Or.inl hcw⟩
      rw [dotProduct_add, h, h1]
      decide
  have hdet : (1 + vecMulVec d ψ).det = 1 := by
    rw [vecMulVec_eq (ι := Fin 1), det_one_add_replicateCol_mul_replicateRow, hd, add_zero]
  have hMv : ∀ x, (1 + vecMulVec d ψ) *ᵥ x = x + (ψ ⬝ᵥ x) • d := fun x => by
    rw [add_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul]
  refine ⟨⟨1 + vecMulVec d ψ, hdet⟩, ?_, ?_⟩
  · show (1 + vecMulVec d ψ) *ᵥ w₂ = w₂
    rw [hMv, h2, zero_smul, add_zero]
  · show (1 + vecMulVec d ψ) *ᵥ w = c ∨ (1 + vecMulVec d ψ) *ᵥ w = w + c
    rw [hMv, h1, one_smul]
    exact hwd

variable {G : Type} [Group G] [Finite G] {T L V H V₂ : Subgroup G}

end CFSG.Quasithin.H13.L32A.C
