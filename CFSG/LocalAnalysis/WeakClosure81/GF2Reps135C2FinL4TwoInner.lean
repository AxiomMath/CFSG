module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL4TwoModule
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL4TwoGraph
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinSp6Two14Jordan

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.WeakClosure81

open Module Matrix CFSG.LargeExtraspecial.SL4Mod CFSG.LargeExtraspecial.SL4Mod.Native

theorem wordProd_inner_one :
    ((wordProd [0, 3, 0] : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1 + jordanD 4 1 := by
  have h := (hasCode_wordProd [0, 3, 0]).toMat_eq
  change ((wordProd [0, 3, 0] : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = _ at h
  rw [h]
  decide +kernel

theorem wordProd_inner_two :
    ((wordProd [4, 2, 5, 0, 3, 2, 0, 4] : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      1 + jordanD 4 2 := by
  have h := (hasCode_wordProd [4, 2, 5, 0, 3, 2, 0, 4]).toMat_eq
  change ((wordProd [4, 2, 5, 0, 3, 2, 0, 4] : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = _ at h
  rw [h]
  decide +kernel

theorem finrank_range_conj {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (e : V ≃ₗ[ZMod 2] V) (f : V →ₗ[ZMod 2] V) :
    finrank (ZMod 2) (LinearMap.range ((e : V →ₗ[ZMod 2] V) ∘ₗ f ∘ₗ (e.symm : V →ₗ[ZMod 2] V))) =
      finrank (ZMod 2) (LinearMap.range f) := by
  rw [LinearMap.range_comp, LinearMap.range_comp_of_range_eq_top f (LinearEquiv.range e.symm),
    LinearEquiv.finrank_map_eq]

theorem four_le_finrank_of_inner {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {d : ℕ}
    (ρ : SL4 →* (V ≃ₗ[ZMod 2] V)) (e : V ≃ₗ[ZMod 2] (Fin d → ZMod 2))
    (M : ℕ → Matrix (Fin d) (Fin d) (ZMod 2))
    (hM : ∀ s < 6, ∀ v, e (ρ (genN s) v) = M s *ᵥ e v)
    (h1 : 4 ≤ finrank (ZMod 2) (LinearMap.range (([0, 3, 0].map M).prod - 1).mulVecLin))
    (h2 : 4 ≤ finrank (ZMod 2)
      (LinearMap.range (([4, 2, 5, 0, 3, 2, 0, 4].map M).prod - 1).mulVecLin))
    (y : SL4) (hy2 : y * y = 1) (hy1 : y ≠ 1) :
    4 ≤ finrank (ZMod 2) (LinearMap.range ((ρ y : V →ₗ[ZMod 2] V) - 1)) := by
  classical
  have hyy : (y : Matrix (Fin 4) (Fin 4) (ZMod 2)) * (y : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1 := by
    have := congrArg (fun z : SL4 => (z : Matrix (Fin 4) (Fin 4) (ZMod 2))) hy2
    simpa using this
  set t : Matrix (Fin 4) (Fin 4) (ZMod 2) := (y : Matrix (Fin 4) (Fin 4) (ZMod 2)) - 1 with ht_def
  have hyt : (y : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1 + t := by
    rw [ht_def]
    abel
  have ht : t * t = 0 := by
    have e1 : t * t = (y : Matrix (Fin 4) (Fin 4) (ZMod 2)) * (y : Matrix (Fin 4) (Fin 4) (ZMod 2))
        + (1 - (y : Matrix (Fin 4) (Fin 4) (ZMod 2)) - (y : Matrix (Fin 4) (Fin 4) (ZMod 2))) := by
      simp only [ht_def, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul]
      abel
    rw [e1, hyy]
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.zero_apply]
    generalize (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) i j = a
    generalize (y : Matrix (Fin 4) (Fin 4) (ZMod 2)) i j = b
    revert a b
    decide
  obtain ⟨P, a, ha, hP⟩ := sq_zero_jordan t ht
  have hPinv : (P : Matrix (Fin 4) (Fin 4) (ZMod 2)) *
      ((P⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1 := Units.mul_inv P
  have hinvP : ((P⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) *
      (P : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1 := Units.inv_mul P
  have htP : t = (P : Matrix (Fin 4) (Fin 4) (ZMod 2)) * jordanD 4 a *
      ((P⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2)) := by
    rw [← hP]
    calc t = ((P : Matrix (Fin 4) (Fin 4) (ZMod 2)) *
          ((P⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))) * t *
          ((P : Matrix (Fin 4) (Fin 4) (ZMod 2)) *
          ((P⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))) := by
          rw [hPinv, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have ha0 : a ≠ 0 := by
    rintro rfl
    have hJ : jordanD 4 0 = 0 := by
      ext i j
      simp [jordanD]
    rw [hJ, Matrix.mul_zero, Matrix.zero_mul] at htP
    apply hy1
    apply Subtype.ext
    rw [hyt, htP, add_zero]
    rfl
  obtain ⟨w, hw6, hwmat, hrank⟩ : ∃ w : List ℕ, (∀ s ∈ w, s < 6) ∧
      ((wordProd w : SL4) : Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1 + jordanD 4 a ∧
      4 ≤ finrank (ZMod 2) (LinearMap.range ((w.map M).prod - 1).mulVecLin) := by
    have ha12 : a = 1 ∨ a = 2 := by omega
    rcases ha12 with rfl | rfl
    · exact ⟨[0, 3, 0], by decide, wordProd_inner_one, h1⟩
    · exact ⟨[4, 2, 5, 0, 3, 2, 0, 4], by decide, wordProd_inner_two, h2⟩
  let p : SL4 := ⟨(P : Matrix (Fin 4) (Fin 4) (ZMod 2)), det_gl_eq_one P⟩
  have hyp : y = p * wordProd w * p⁻¹ := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hwmat,
      coe_sl_inv_eq_gl_inv (B := P) (b := p) rfl, hyt, htP]
    show _ = (P : Matrix (Fin 4) (Fin 4) (ZMod 2)) * (1 + jordanD 4 a) *
      ((P⁻¹ : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hPinv]
  have hconj : ((ρ y : V →ₗ[ZMod 2] V) - 1) = (ρ p : V →ₗ[ZMod 2] V) ∘ₗ
      (((ρ (wordProd w) : V →ₗ[ZMod 2] V) - 1) ∘ₗ ((ρ p).symm : V →ₗ[ZMod 2] V)) := by
    apply LinearMap.ext
    intro v
    rw [hyp, map_mul, map_mul, map_inv]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, map_sub,
      LinearEquiv.mul_apply, Module.End.one_apply, LinearEquiv.apply_symm_apply]
    rfl
  have hrk : finrank (ZMod 2) (LinearMap.range ((ρ y : V →ₗ[ZMod 2] V) - 1)) =
      finrank (ZMod 2) (LinearMap.range ((ρ (wordProd w) : V →ₗ[ZMod 2] V) - 1)) := by
    rw [hconj]
    exact finrank_range_conj (ρ p) _
  rw [hrk, finrank_range_sub_one_eq e (ρ (wordProd w)) ((w.map M).prod)
    (equiv_act_wordProd ρ e M hM w hw6)]
  exact hrank

end CFSG.LocalAnalysis.WeakClosure81
