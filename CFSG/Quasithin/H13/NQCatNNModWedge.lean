module

public import CFSG.Quasithin.Background.JonesParshallWedgeH1
public import CFSG.Quasithin.Background.FFC4Five

public section

open Matrix CFSG.Quasithin.JonesParshall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.NQCat.NNMod

section Fix

@[expose] def e10 (l : Fin 10) : Fin 10 → ZMod 2 := fun l' => if l' = l then 1 else 0

theorem eq_zero_of_row {W : Matrix (Fin 10) (Fin 10) (ZMod 2)} {k l : Fin 10}
    (hrow : ∀ l', W k l' = (1 : Matrix (Fin 10) (Fin 10) (ZMod 2)) k l' + e10 l l')
    {m : Fin 10 → ZMod 2} (hm : W *ᵥ m = m) : m l = 0 := by
  have h := congrFun hm k
  simp only [mulVec, dotProduct, hrow, add_mul, Finset.sum_add_distrib] at h
  have h1 : ∑ l', (1 : Matrix (Fin 10) (Fin 10) (ZMod 2)) k l' * m l' = m k := by
    simp [Matrix.one_apply]
  have h2 : ∑ l', e10 l l' * m l' = m l := by
    simp [e10]
  rw [h1, h2] at h
  linear_combination h

@[expose] def T20 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 1, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

@[expose] def T21 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 1, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

@[expose] def T23 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 1, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

@[expose] def T32 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 1, 1, 0; 0, 0, 0, 0, 1]

@[expose] def T42 : Matrix (Fin 5) (Fin 5) (ZMod 2) :=
  !![1, 0, 0, 0, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 1]

@[expose] def tv : Fin 5 → Matrix (Fin 5) (Fin 5) (ZMod 2) := ![T20, T21, T23, T32, T42]

theorem eq_zero_of_fix {m : Fin 10 → ZMod 2} (h : ∀ i, wedgeMat (tv i) *ᵥ m = m) : m = 0 := by
  have h20 : wedgeMat T20 *ᵥ m = m := h 0
  have h21 : wedgeMat T21 *ᵥ m = m := h 1
  have h23 : wedgeMat T23 *ᵥ m = m := h 2
  have h32 : wedgeMat T32 *ᵥ m = m := h 3
  have h42 : wedgeMat T42 *ᵥ m = m := h 4
  funext l
  fin_cases l
  · exact eq_zero_of_row (k := 4) (by decide) h20
  · exact eq_zero_of_row (k := 2) (by decide) h32
  · exact eq_zero_of_row (k := 7) (by decide) h20
  · exact eq_zero_of_row (k := 8) (by decide) h20
  · exact eq_zero_of_row (k := 5) (by decide) h32
  · exact eq_zero_of_row (k := 7) (by decide) h21
  · exact eq_zero_of_row (k := 8) (by decide) h21
  · exact eq_zero_of_row (k := 9) (by decide) h42
  · exact eq_zero_of_row (k := 9) (by decide) h32
  · exact eq_zero_of_row (k := 8) (by decide) h23

theorem fix_transpose (i : Fin 5) : wedgeMat (tv i)ᵀ *ᵥ e10 0 = e10 0 := by
  fin_cases i <;> decide

theorem tv_mul_self (i : Fin 5) : tv i * tv i = 1 := by
  fin_cases i <;> decide

theorem det_tv (i : Fin 5) : (tv i).det = 1 := by
  have h := congrArg Matrix.det (tv_mul_self i)
  rw [det_mul, det_one] at h
  have key : ∀ x : ZMod 2, x * x = 1 → x = 1 := by decide
  exact key _ h

end Fix

section Twist

@[expose] def tvSL (i : Fin 5) : SpecialLinearGroup (Fin 5) (ZMod 2) := ⟨tv i, det_tv i⟩

theorem tvSL_inv (i : Fin 5) : (tvSL i)⁻¹ = tvSL i := by
  refine inv_eq_of_mul_eq_one_right (Subtype.ext ?_)
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
  exact tv_mul_self i

theorem wedgeMat_mul_mulVec (g h : SpecialLinearGroup (Fin 5) (ZMod 2)) (v : Fin 10 → ZMod 2) :
    wedgeMat ((g * h : SpecialLinearGroup (Fin 5) (ZMod 2)) :
      Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ v =
      wedgeMat (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ
        (wedgeMat (h : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ v) := by
  rw [← muW_apply, ← muW_apply, ← muW_apply, map_mul]
  rfl

theorem wedgeMat_one_mulVec (v : Fin 10 → ZMod 2) :
    wedgeMat ((1 : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ v =
      v := by
  rw [← muW_apply, map_one]
  rfl

theorem false_of_wedge {V : Type*} [CommGroup V] (F : V →* Multiplicative (Fin 10 → ZMod 2))
    (hFs : Function.Surjective F) (ρ : SpecialLinearGroup (Fin 5) (ZMod 2) →* MulAut V)
    (hρ : ∀ g w, Multiplicative.toAdd (F (ρ g w)) =
      wedgeMat (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ Multiplicative.toAdd (F w))
    (τ : MulAut V) (hτ : ∀ w, F w = 1 → F (τ w) = 1) (hτ' : ∀ w, F w = 1 → F (τ⁻¹ w) = 1)
    (α : SpecialLinearGroup (Fin 5) (ZMod 2) → SpecialLinearGroup (Fin 5) (ZMod 2))
    (hα : ∀ g, ρ (α g) = τ * ρ g * τ⁻¹) (A : SpecialLinearGroup (Fin 5) (ZMod 2))
    (hA : ∀ g, ((α g : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
      (A : Matrix (Fin 5) (Fin 5) (ZMod 2)) *
        ((g⁻¹ : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ *
          ((A⁻¹ : SpecialLinearGroup (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2))) :
    False := by
  set m₀ : Fin 10 → ZMod 2 := e10 0 with hm₀
  set m₁ : Fin 10 → ZMod 2 := wedgeMat (A : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ m₀ with hm₁
  obtain ⟨w₀, hw₀⟩ := hFs (Multiplicative.ofAdd m₁)
  set w₁ := τ⁻¹ w₀ with hw₁
  have hfix1 : ∀ i, wedgeMat ((α (tvSL i) : SpecialLinearGroup (Fin 5) (ZMod 2)) :
      Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ m₁ = m₁ := by
    intro i
    set tT : SpecialLinearGroup (Fin 5) (ZMod 2) := ⟨(tv i)ᵀ, by rw [det_transpose, det_tv]⟩
    have hαt : α (tvSL i) = A * tT * A⁻¹ := by
      apply Subtype.ext
      rw [hA, tvSL_inv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
      rfl
    rw [hαt, wedgeMat_mul_mulVec, wedgeMat_mul_mulVec, hm₁, ← wedgeMat_mul_mulVec A⁻¹ A,
      inv_mul_cancel, wedgeMat_one_mulVec]
    congr 1
    exact fix_transpose i
  have hfix2 : ∀ i, wedgeMat (tv i) *ᵥ Multiplicative.toAdd (F w₁) =
      Multiplicative.toAdd (F w₁) := by
    intro i
    have h1 : τ (ρ (tvSL i) w₁) = ρ (α (tvSL i)) w₀ := by
      rw [hα]
      simp [hw₁, MulAut.mul_apply]
    have h2 : F (ρ (α (tvSL i)) w₀) = F w₀ := by
      apply Multiplicative.toAdd.injective
      rw [hρ, hw₀, toAdd_ofAdd, hfix1]
    have h3 : F (τ (ρ (tvSL i) w₁ * w₁⁻¹)) = 1 := by
      rw [map_mul, map_inv, h1, map_mul, map_inv, h2, hw₁, MulAut.apply_inv_self]
      exact mul_inv_cancel _
    have h4 := hτ' _ h3
    rw [MulAut.inv_apply_self, map_mul, map_inv] at h4
    have h5 : F (ρ (tvSL i) w₁) = F w₁ := mul_inv_eq_one.1 h4
    have h6 := hρ (tvSL i) w₁
    rw [h5] at h6
    exact h6.symm
  have hz := eq_zero_of_fix hfix2
  have hF1 : F w₁ = 1 := by
    apply Multiplicative.toAdd.injective
    rw [hz]
    rfl
  have hF0 := hτ _ hF1
  rw [hw₁, MulAut.apply_inv_self, hw₀] at hF0
  have hm1 : m₁ = 0 := by
    have := congrArg Multiplicative.toAdd hF0
    simpa using this
  have hm0 : m₀ = 0 := by
    have h := congrArg (fun v => wedgeMat ((A⁻¹ : SpecialLinearGroup (Fin 5) (ZMod 2)) :
      Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ v) hm1
    simp only [hm₁] at h
    rw [← wedgeMat_mul_mulVec, inv_mul_cancel, wedgeMat_one_mulVec, mulVec_zero] at h
    exact h
  have := congrFun hm0 0
  simp [hm₀, e10] at this

end Twist

section Coord

open CFSG.Assembly.LowTwoRank

theorem exists_wedgeMap {V : Type*} [CommGroup V] {H : Subgroup (MulAut V)} {U : Subgroup V}
    {π : ↥(StatedSL 5 (ZMod 2)) →* ↥H} (h : (FFModel.extSq (ZMod 2) 5).RealizesVia H U ⊥ π)
    (hsup : U ⊔ fixV H = ⊤) (hinf : U ⊓ fixV H = ⊥) :
    ∃ F : V →* Multiplicative (Fin 10 → ZMod 2), Function.Surjective F ∧
      (∀ w, F w = 1 ↔ w ∈ fixV H) ∧
      ∀ (γ : ↥(StatedSL 5 (ZMod 2))) (w : V),
        Multiplicative.toAdd (F (((π γ : ↥H) : MulAut V) w)) =
          wedgeMat ((γ : GL (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)) *ᵥ
            Multiplicative.toAdd (F w) := by
  obtain ⟨q, -, hqs, hqk, hqe⟩ := FFC.exists_modelHom rfl h hsup hinf
  let q' : V →* Multiplicative (⋀[ZMod 2]^2 (Fin 5 → ZMod 2)) := q
  have hq' : ∀ w, q' w = q w := fun _ => rfl
  let E : Multiplicative (⋀[ZMod 2]^2 (Fin 5 → ZMod 2)) ≃* Multiplicative (Fin 10 → ZMod 2) :=
    AddEquiv.toMultiplicative (wedgeEquiv (ZMod 2)).toAddEquiv
  refine ⟨E.toMonoidHom.comp q', fun y => ?_, fun w => ?_, fun γ w => ?_⟩
  · obtain ⟨w, hw⟩ := hqs (E.symm y) trivial
    refine ⟨w, ?_⟩
    rw [MonoidHom.comp_apply, hq', hw]
    exact E.apply_symm_apply y
  · rw [← hqk w, MonoidHom.comp_apply, hq']
    exact E.map_eq_one_iff
  · have e1 : q' (((π γ : ↥H) : MulAut V) w) = Multiplicative.ofAdd (exteriorPower.map 2
        (Matrix.toLin' ((γ : GL (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)))
          (Multiplicative.toAdd (q' w))) := hqe γ w
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, e1]
    change wedgeEquiv (ZMod 2) (exteriorPower.map 2 (Matrix.toLin'
      ((γ : GL (Fin 5) (ZMod 2)) : Matrix (Fin 5) (Fin 5) (ZMod 2)))
        (Multiplicative.toAdd (q' w))) = _
    rw [wedgeEquiv_apply, wedgeCoord_map]
    rfl

end Coord

end CFSG.Quasithin.H13.NQCat.NNMod
