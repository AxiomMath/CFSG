module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowZDet

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType

open CFSG.Assembly

private theorem ggDetLin_coord {p k : ℕ} [Fact p.Prime] {H : Type} [CommGroup H]
    [Module (ZMod p) (Additive H)] (s : MulAut H) (e0 : H ≃* Multiplicative (Fin k → ZMod p))
    (M : Matrix (Fin k) (Fin k) (ZMod p))
    (hM : ∀ f : Fin k → ZMod p,
      Multiplicative.toAdd (e0 (s (e0.symm (Multiplicative.ofAdd f)))) = M.mulVec f) :
    ((ggDetLin (p := p) s : (ZMod p)ˣ) : ZMod p) = M.det := by
  let eA : Additive H ≃+ (Fin k → ZMod p) :=
    { toFun := fun x => Multiplicative.toAdd (e0 (Additive.toMul x))
      invFun := fun v => Additive.ofMul (e0.symm (Multiplicative.ofAdd v))
      left_inv := fun x => by simp
      right_inv := fun v => by simp
      map_add' := fun x y => by simp }
  let e : Additive H ≃ₗ[ZMod p] (Fin k → ZMod p) :=
    eA.toLinearEquiv fun c x => ZMod.map_smul eA c x
  have h : (e : Additive H →ₗ[ZMod p] (Fin k → ZMod p)) ∘ₗ
      ((ggLinAut (p := p) s : Additive H ≃ₗ[ZMod p] Additive H) :
        Additive H →ₗ[ZMod p] Additive H) ∘ₗ
      (e.symm : (Fin k → ZMod p) →ₗ[ZMod p] Additive H) = Matrix.toLin' M := by
    refine LinearMap.ext fun f => ?_
    exact (hM f).trans (Matrix.toLin'_apply M f).symm
  rw [ggDetLin, MonoidHom.comp_apply, LinearEquiv.coe_det, ← LinearMap.det_conj _ e, h,
    LinearMap.det_toLin']

theorem ggDetAut_coord {p k : ℕ} (hP : p.Prime) {H : Type} [Group H]
    (hc : ∀ a b : H, a * b = b * a) (hp : ∀ a : H, a ^ p = 1) (s : MulAut H)
    (e0 : H ≃* Multiplicative (Fin k → ZMod p)) (M : Matrix (Fin k) (Fin k) (ZMod p))
    (hM : ∀ f : Fin k → ZMod p,
      Multiplicative.toAdd (e0 (s (e0.symm (Multiplicative.ofAdd f)))) = M.mulVec f) :
    ((ggDetAut p hP hc hp s : (ZMod p)ˣ) : ZMod p) = M.det := by
  haveI : Fact p.Prime := ⟨hP⟩
  letI : CommGroup H := { (inferInstance : Group H) with mul_comm := hc }
  letI : Module (ZMod p) (Additive H) := AddCommGroup.zmodModule (n := p) fun a => by
    have h : (Additive.toMul a) ^ p = 1 := hp _
    rw [← ofMul_toMul a, ← ofMul_pow, h, ofMul_one]
  exact ggDetLin_coord s e0 M hM

@[expose] def ggScaleCoord {p N : ℕ} (u : (ZMod p)ˣ) (i : Fin N) :
    MulAut (Multiplicative (Fin N → ZMod p)) :=
  AddEquiv.toMultiplicative
    { toFun := fun v => Function.update v i ((u : ZMod p) * v i)
      invFun := fun v => Function.update v i (((u⁻¹ : (ZMod p)ˣ) : ZMod p) * v i)
      left_inv := fun v => by
        funext j
        by_cases h : j = i
        · subst h
          simp
        · simp [Function.update_of_ne h]
      right_inv := fun v => by
        funext j
        by_cases h : j = i
        · subst h
          simp
        · simp [Function.update_of_ne h]
      map_add' := fun v w => by
        funext j
        by_cases h : j = i
        · subst h
          simp [mul_add]
        · simp [Function.update_of_ne h] }

theorem ggScaleCoord_apply {p N : ℕ} (u : (ZMod p)ˣ) (i : Fin N) (v : Fin N → ZMod p) :
    ggScaleCoord u i (Multiplicative.ofAdd v) =
      Multiplicative.ofAdd (Function.update v i ((u : ZMod p) * v i)) :=
  rfl

theorem ggDetAut_ggScaleCoord {p N : ℕ} (hP : p.Prime) (u : (ZMod p)ˣ) (i : Fin N)
    (hc : ∀ a b : Multiplicative (Fin N → ZMod p), a * b = b * a)
    (hp : ∀ a : Multiplicative (Fin N → ZMod p), a ^ p = 1) :
    ggDetAut p hP hc hp (ggScaleCoord u i) = u := by
  refine Units.ext ?_
  rw [ggDetAut_coord hP hc hp (ggScaleCoord u i) (MulEquiv.refl _)
    (Matrix.diagonal (Function.update (1 : Fin N → ZMod p) i (u : ZMod p)))]
  · rw [Matrix.det_diagonal, Fintype.prod_eq_single i]
    · simp
    · intro j hj
      simp [Function.update_of_ne hj]
  · intro f
    show Multiplicative.toAdd (ggScaleCoord u i (Multiplicative.ofAdd f)) = _
    rw [ggScaleCoord_apply, toAdd_ofAdd]
    funext j
    rw [Matrix.mulVec_diagonal]
    by_cases h : j = i
    · subst h
      simp
    · simp [Function.update_of_ne h]

end CFSG.StandardType

end
