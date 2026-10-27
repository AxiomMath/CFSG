module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Even.Aut
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.Quasithin.Vol2.GoldschmidtH11Base

public section

open scoped MatrixGroups

namespace CFSG.Quasithin.H11

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo
  CFSG.SignalizerFunctorTheorem.McBride.PSL2Even

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
theorem mk_injective :
    Function.Injective (QuotientGroup.mk' (Subgroup.center SL(2, F))) := by
  intro x y hxy
  have h : x⁻¹ * y ∈ Subgroup.center SL(2, F) := QuotientGroup.eq.mp hxy
  rw [CFSG.Walter.sl2_center_eq_bot_of_charTwo, Subgroup.mem_bot] at h
  exact inv_mul_eq_one.mp h

theorem exists_aut_formula (θ : MulAut SL(2, F)) :
    ∃ (ψ : F ≃+* F) (h : SL(2, F)),
      ∀ γ, θ γ = h * Matrix.SpecialLinearGroup.map ψ.toRingHom γ * h⁻¹ := by
  classical
  have hc : Subgroup.center SL(2, F) = ⊥ := CFSG.Walter.sl2_center_eq_bot_of_charTwo
  let mk : SL(2, F) →* PSL(2, F) := QuotientGroup.mk' (Subgroup.center _)
  let θ' : MulAut PSL(2, F) :=
    QuotientGroup.congr (Subgroup.center _) (Subgroup.center _) θ (by rw [hc]; simp)
  have hθ' : ∀ x, θ' (mk x) = mk (θ x) := fun x => rfl
  obtain ⟨w, hw⟩ := semilinearAction_surjective F θ'
  obtain ⟨y₀, hy₀⟩ := toPGL_surjective F w.left
  obtain ⟨h, rfl⟩ : ∃ h, mk h = y₀ := QuotientGroup.mk_surjective y₀
  refine ⟨w.right, h, fun γ => mk_injective ?_⟩
  have key : θ' (mk γ) = pglAction F w.left (psl2FieldAut F w.right (mk γ)) := by
    rw [← hw, ← SemidirectProduct.inl_left_mul_inr_right w, map_mul, semilinearAction_inl,
      semilinearAction_inr]
    simp
  have e1 : psl2RingEquiv w.right (mk γ) = mk (Matrix.SpecialLinearGroup.map w.right.toRingHom γ) :=
    psl2RingEquiv_mk w.right γ
  rw [← hθ', key, ← hy₀, pglAction_toPGL]
  simp only [MulAut.conj_apply, psl2FieldAut_apply, e1, map_mul, map_inv]
  rfl

omit [Finite F] in
theorem eq_one_of_aut_formula (ψ : F ≃+* F) (z : SL(2, F))
    (h : ∀ γ, z * Matrix.SpecialLinearGroup.map ψ.toRingHom γ * z⁻¹ = γ) : ψ = 1 ∧ z = 1 := by
  have hu : ∀ c, (z : Matrix (Fin 2) (Fin 2) F) * !![1, ψ c; 0, 1] = !![1, c; 0, 1] * z := by
    intro c
    have := congrArg (fun x : SL(2, F) => x * z) (h (uSL c))
    simp only [inv_mul_cancel_right, map_uSL] at this
    have := congrArg Subtype.val this
    simpa [Matrix.SpecialLinearGroup.coe_mul, coe_uSL] using this
  have hl : ∀ c, (z : Matrix (Fin 2) (Fin 2) F) * !![1, 0; ψ c, 1] = !![1, 0; c, 1] * z := by
    intro c
    have := congrArg (fun x : SL(2, F) => x * z) (h (lSL c))
    simp only [inv_mul_cancel_right, map_lSL] at this
    have := congrArg Subtype.val this
    simpa [Matrix.SpecialLinearGroup.coe_mul, coe_lSL] using this
  have hdet := z.2
  rw [Matrix.det_fin_two] at hdet
  have h00 := congrFun (congrFun (hu 1) 0) 0
  have h01 := congrFun (congrFun (hu 1) 0) 1
  have h11 := congrFun (congrFun (hl 1) 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h11
  have hps : (z : Matrix (Fin 2) (Fin 2) F) 0 0 = (z : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    linear_combination h01
  have hp : (z : Matrix (Fin 2) (Fin 2) F) 0 0 = 1 := by
    apply eq_one_of_mul_self_eq_one
    rw [h00, h11] at hdet
    nth_rewrite 2 [hps]
    linear_combination hdet
  have hs : (z : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := hps ▸ hp
  refine ⟨RingEquiv.ext fun c => ?_, Subtype.ext ?_⟩
  · have hc := congrFun (congrFun (hu c) 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, hp, hs] at hc
    show ψ c = (1 : F ≃+* F) c
    simpa using add_right_cancel (hc.trans (add_comm _ _))
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h11, hp, hs]

end CFSG.Quasithin.H11
