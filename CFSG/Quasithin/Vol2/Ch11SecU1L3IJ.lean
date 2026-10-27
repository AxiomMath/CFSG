module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80L3Syl

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.L3I

open Matrix CFSG.Quasithin.E2P.Asc80
open scoped MatrixGroups

section TwoByTwo

variable {F : Type*} [Field F]

@[expose] def sl2U (F : Type*) [Field F] : SL(2, F) := ⟨!![1, 1; 0, 1], by simp [det_fin_two]⟩

@[expose] def sl2L (F : Type*) [Field F] : SL(2, F) := ⟨!![1, 0; 1, 1], by simp [det_fin_two]⟩

theorem eq_scalar_of_commute_sl2 {A : GL (Fin 2) F}
    (h : ∀ S : SL(2, F), A * Matrix.SpecialLinearGroup.toGL S =
      Matrix.SpecialLinearGroup.toGL S * A) :
    ∃ u : Fˣ, A = Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
  have hU : (A : Matrix (Fin 2) (Fin 2) F) * !![1, 1; 0, 1] =
      !![1, 1; 0, 1] * (A : Matrix (Fin 2) (Fin 2) F) := congrArg Units.val (h (sl2U F))
  have hL : (A : Matrix (Fin 2) (Fin 2) F) * !![1, 0; 1, 1] =
      !![1, 0; 1, 1] * (A : Matrix (Fin 2) (Fin 2) F) := congrArg Units.val (h (sl2L F))
  have e1 := congrFun (congrFun hU 0) 1
  have e2 := congrFun (congrFun hU 1) 1
  have e3 := congrFun (congrFun hL 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e1 e2 e3
  have h10 : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by linear_combination e2
  have h01 : (A : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by linear_combination e3
  have h11 : (A : Matrix (Fin 2) (Fin 2) F) 1 1 = (A : Matrix (Fin 2) (Fin 2) F) 0 0 := by
    linear_combination -e1
  have hdet : (A : Matrix (Fin 2) (Fin 2) F).det ≠ 0 := (Matrix.isUnits_det_units A).ne_zero
  have h00 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := fun h0 => hdet (by
    rw [det_fin_two, h0, h01]
    ring)
  refine ⟨Units.mk0 _ h00, Units.ext ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h10, h01, h11]

theorem det_eq_neg_one_of_mul_self {A : GL (Fin 2) F} (hA : A * A = 1)
    (hA1 : A ≠ 1) (hA2 : A ≠ -1) : (A : Matrix (Fin 2) (Fin 2) F).det = -1 := by
  have hM : (A : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F) = 1 :=
    congrArg Units.val hA
  have e00 := congrFun (congrFun hM 0) 0
  have e01 := congrFun (congrFun hM 0) 1
  have e10 := congrFun (congrFun hM 1) 0
  have e11 := congrFun (congrFun hM 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  rw [det_fin_two]
  set a := (A : Matrix (Fin 2) (Fin 2) F) 0 0
  set b := (A : Matrix (Fin 2) (Fin 2) F) 0 1
  set c := (A : Matrix (Fin 2) (Fin 2) F) 1 0
  set d := (A : Matrix (Fin 2) (Fin 2) F) 1 1
  by_cases hs : a + d = 0
  · have hd : d = -a := by linear_combination hs
    rw [hd]
    linear_combination -e00
  · exfalso
    have hb : b = 0 := (mul_eq_zero.mp (by linear_combination e01 : b * (a + d) = 0)).resolve_right
      hs
    have hc : c = 0 := (mul_eq_zero.mp (by linear_combination e10 : c * (a + d) = 0)).resolve_right
      hs
    rw [hb, hc] at e00 e11
    have had : a = d := by
      have h1 : (a - d) * (a + d) = 0 := by linear_combination e00 - e11
      linear_combination (mul_eq_zero.mp h1).resolve_right hs
    have ha : a = 1 ∨ a = -1 := by
      have h1 : (a - 1) * (a + 1) = 0 := by linear_combination e00
      rcases mul_eq_zero.mp h1 with h | h
      · exact Or.inl (by linear_combination h)
      · exact Or.inr (by linear_combination h)
    rcases ha with ha | ha
    · apply hA1
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [a, b, c, d] at ha hb hc had ⊢ <;>
        simp_all
    · apply hA2
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;> simp [a, b, c, d] at ha hb hc had ⊢ <;>
        simp_all

end TwoByTwo

section Levi

variable {p : ℕ} [Fact p.Prime]

@[expose] noncomputable def leviPsi (p : ℕ) [Fact p.Prime] : GL (Fin 2) (ZMod p) →* PSL3 p :=
  (piL p).comp (leviHom p)

theorem leviPsi_range : (leviPsi p).range = leviC p := by
  rw [leviPsi, MonoidHom.range_comp]
  rfl

theorem leviPsi_neg_one : leviPsi p (-1) = zc p := rfl

theorem leviPsi_eq_one_iff {A : GL (Fin 2) (ZMod p)} :
    leviPsi p A = 1 ↔
      ∃ μ : (ZMod p)ˣ, μ ^ 3 = 1 ∧ A = Matrix.GeneralLinearGroup.scalar (Fin 2) μ := by
  constructor
  · intro h
    have hk : leviHom p A ∈ (piL p).ker := h
    rw [ker_piL] at hk
    obtain ⟨r, hr3, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hk
    rw [Fintype.card_fin] at hr3
    have hr0 : r ≠ 0 := fun h0 => by rw [h0] at hr3; simp at hr3
    have hm := fun i j => congrFun (congrFun hr i) j
    rw [coe_leviHom] at hm
    have h00 := hm 0 0
    have h01 := hm 0 1
    have h10 := hm 1 0
    have h11 := hm 1 1
    simp [Matrix.scalar_apply] at h00 h01 h10 h11
    refine ⟨Units.mk0 r hr0, Units.ext (by simpa using hr3), Units.ext ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [← h00, ← h01, ← h10, ← h11]
  · rintro ⟨μ, hμ, rfl⟩
    have hk : leviHom p (Matrix.GeneralLinearGroup.scalar (Fin 2) μ) ∈
        Subgroup.center SL(3, ZMod p) := by
      have hμ' : (μ : ZMod p) ^ 3 = 1 := by simpa using congrArg Units.val hμ
      have hμ2 : ((μ : ZMod p) ^ 2)⁻¹ = μ := by
        have h0 : (μ : ZMod p) ≠ 0 := μ.ne_zero
        rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (pow_ne_zero 2 h0)]
        linear_combination hμ'
      refine Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨μ, by rw [Fintype.card_fin]; exact hμ',
        ?_⟩
      rw [coe_leviHom]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, hμ2]
    rw [← ker_piL] at hk
    exact hk

theorem leviPsi_scalar_eq_one {μ : (ZMod p)ˣ} (hμ : μ ^ 3 = 1) :
    leviPsi p (Matrix.GeneralLinearGroup.scalar (Fin 2) μ) = 1 :=
  leviPsi_eq_one_iff.mpr ⟨μ, hμ, rfl⟩

@[expose] noncomputable def leviY (p : ℕ) [Fact p.Prime] : Subgroup (PSL3 p) := (ofSL2 p).range

theorem ofSL2_eq_leviPsi (A : SL(2, ZMod p)) :
    ofSL2 p A = leviPsi p (Matrix.SpecialLinearGroup.toGL A) := rfl

theorem leviY_le_leviC : leviY p ≤ leviC p := by
  rintro _ ⟨A, rfl⟩
  exact ofSL2_mem_leviC A

theorem ofSL2_injective : Function.Injective (ofSL2 p) := by
  rw [injective_iff_map_eq_one]
  intro A hA
  have h1 := eq_one_of_piL_leviHom_eq_one (X := Matrix.SpecialLinearGroup.toGL A) A.2 hA
  exact Matrix.SpecialLinearGroup.toGL_injective (h1.trans (map_one _).symm)

theorem zc_mem_leviY : zc p ∈ leviY p := by
  refine ⟨-1, ?_⟩
  rw [ofSL2_eq_leviPsi, ← leviPsi_neg_one]
  congr 1
  apply Units.ext
  simp

end Levi

end CFSG.Quasithin.Vol2.Ch11.SecU1.L3I
