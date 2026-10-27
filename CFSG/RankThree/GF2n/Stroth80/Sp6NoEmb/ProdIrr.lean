module

public import CFSG.LocalAnalysis.ComponentInitial.PairedBinaryLinearThreeTensorOrbitsGeneral

public noncomputable section

namespace CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb

open Module
open scoped TensorProduct
open CFSG.LocalAnalysis.ComponentInitial.PairedTensorOrbits (AbsIrr outer outer_apply outer_tmul
  IsInv subrepOf exists_minimal isIrreducible_subrepOf isIrreducible_iff)
open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace (nonempty_equiv_of_ne_zero)
open CFSG.LocalAnalysis.ComponentInitial

universe u

section Tensor

variable {k G V X Y : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V] [AddCommGroup X]
  [Module k X] [AddCommGroup Y] [Module k Y]

theorem eq_zero_of_forall_lTensor {t : X ⊗[k] Y}
    (h : ∀ φ : Module.Dual k Y, TensorProduct.rid k X (LinearMap.lTensor X φ t) = 0) : t = 0 := by
  classical
  let b := Basis.ofVectorSpace k Y
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  rw [map_zero]
  ext i
  rw [TensorProduct.equivFinsuppOfBasisRight_apply, Finsupp.zero_apply]
  exact h (b.coord i)

theorem tmul_ne_zero_of_ne_zero {x : X} {y : Y} (hx : x ≠ 0) (hy : y ≠ 0) : x ⊗ₜ[k] y ≠ 0 := by
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one k hy
  intro h
  have h1 := congrArg (fun t => TensorProduct.rid k X (LinearMap.lTensor X φ t)) h
  simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul, hφ, one_smul, map_zero] at h1
  exact hx h1

theorem exists_ne_zero_of_tensor (π : Representation k G V) (ρ : Representation k G X)
    (f : V →ₗ[k] X ⊗[k] Y) (hf : ∀ g v, f (π g v) = TensorProduct.map (ρ g) LinearMap.id (f v))
    (hne : f ≠ 0) : ∃ F : V →ₗ[k] X, (∀ g v, F (π g v) = ρ g (F v)) ∧ F ≠ 0 := by
  obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne (LinearMap.ext hcon)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k Y,
      TensorProduct.rid k X (LinearMap.lTensor X φ (f v)) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv (eq_zero_of_forall_lTensor hcon)
  refine ⟨(TensorProduct.rid k X).toLinearMap ∘ₗ LinearMap.lTensor X φ ∘ₗ f, fun g w => ?_,
    fun h0 => hφ (LinearMap.congr_fun h0 v)⟩
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, hf]
  generalize f w = t
  induction t with
  | tmul a c =>
    rw [TensorProduct.map_tmul, LinearMap.lTensor_tmul, LinearMap.lTensor_tmul,
      TensorProduct.rid_tmul, TensorProduct.rid_tmul, LinearMap.id_apply, map_smul]
  | add t t' ht ht' => simp only [map_add, ht, ht']

theorem nonempty_equiv_of_tensor {E : Type*} [AddCommGroup E] [Module k E]
    {σ : Representation k G E} (hσ : σ.IsIrreducible) {ρ : Representation k G X}
    (hρ : ρ.IsIrreducible) (f : E →ₗ[k] X ⊗[k] Y)
    (hf : ∀ g v, f (σ g v) = TensorProduct.map (ρ g) LinearMap.id (f v)) (hne : f ≠ 0) :
    Nonempty (σ.Equiv ρ) := by
  obtain ⟨F, hF, hF0⟩ := exists_ne_zero_of_tensor σ ρ f hf hne
  obtain ⟨e⟩ := nonempty_equiv_of_ne_zero hρ hσ F hF hF0
  exact ⟨e.symm⟩

theorem nonempty_equiv_of_tensorEquiv {E : Type*} [AddCommGroup E] [Module k E]
    {σ : Representation k G E} (hσ : σ.IsIrreducible) {τ : Representation k G V}
    {ρ : Representation k G X} (hρ : ρ.IsIrreducible) (e : V ≃ₗ[k] X ⊗[k] Y)
    (he : ∀ g v, e (τ g v) = TensorProduct.map (ρ g) LinearMap.id (e v)) (f : E →ₗ[k] V)
    (hf : ∀ g v, f (σ g v) = τ g (f v)) (hne : f ≠ 0) : Nonempty (σ.Equiv ρ) := by
  refine nonempty_equiv_of_tensor hσ hρ (e.toLinearMap ∘ₗ f) (fun g v => ?_) fun h0 => hne ?_
  · simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, hf, he]
  · ext v
    have h1 := LinearMap.congr_fun h0 v
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearMap.zero_apply, LinearEquiv.map_eq_zero_iff] at h1
    rw [h1, LinearMap.zero_apply]

end Tensor

section Hom

variable {k G₁ G₂ U W : Type*} [Field k] [Group G₁] [Group G₂] [AddCommGroup U] [Module k U]
  [AddCommGroup W] [Module k W]

@[expose] def homSpace (τ : Representation k (G₁ × G₂) U) (A : Representation k G₁ W) :
    Submodule k (W →ₗ[k] U) where
  carrier := {φ | ∀ g x, φ (A g x) = τ (g, 1) (φ x)}
  add_mem' {φ ψ} hφ hψ g x := by
    rw [LinearMap.add_apply, LinearMap.add_apply, hφ, hψ, map_add]
  zero_mem' g x := by rw [LinearMap.zero_apply, LinearMap.zero_apply, map_zero]
  smul_mem' c φ hφ g x := by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, hφ, map_smul]

variable (W) in
@[expose] def homRep (τ : Representation k (G₁ × G₂) U) : Representation k G₂ (W →ₗ[k] U) where
  toFun h :=
    { toFun := fun φ => τ (1, h) ∘ₗ φ
      map_add' := fun φ ψ => LinearMap.comp_add _ _ _
      map_smul' := fun c φ => LinearMap.comp_smul _ _ _ }
  map_one' := LinearMap.ext fun φ => LinearMap.ext fun x => by
    change τ (1, 1) (φ x) = φ x
    rw [show ((1, 1) : G₁ × G₂) = 1 from rfl, map_one, Module.End.one_apply]
  map_mul' h h' := LinearMap.ext fun φ => LinearMap.ext fun x => by
    change τ (1, h * h') (φ x) = τ (1, h) (τ (1, h') (φ x))
    rw [show ((1, h * h') : G₁ × G₂) = (1, h) * (1, h') by rw [Prod.mk_mul_mk, one_mul], map_mul,
      Module.End.mul_apply]

theorem homRep_apply (τ : Representation k (G₁ × G₂) U) (h : G₂) (φ : W →ₗ[k] U) (x : W) :
    homRep W τ h φ x = τ (1, h) (φ x) :=
  rfl

theorem rep_one_mul (τ : Representation k (G₁ × G₂) U) (g : G₁) (h : G₂) (v : U) :
    τ (1, h) (τ (g, 1) v) = τ (g, h) v := by
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, mul_one]

theorem isInv_homSpace (τ : Representation k (G₁ × G₂) U) (A : Representation k G₁ W) :
    IsInv (homRep W τ) (homSpace τ A) := by
  intro h φ hφ g x
  rw [homRep_apply, homRep_apply, hφ, rep_one_mul, ← Module.End.mul_apply, ← map_mul,
    Prod.mk_mul_mk, one_mul, mul_one]

theorem lift_flip_outer (τ : Representation k (G₁ × G₂) U) (A : Representation k G₁ W)
    {W' : Type*} [AddCommGroup W'] [Module k W'] (B : Representation k G₂ W')
    (Φ : W' →ₗ[k] W →ₗ[k] U) (hΦ : ∀ y, Φ y ∈ homSpace τ A)
    (hΦeq : ∀ h y, Φ (B h y) = homRep W τ h (Φ y)) (p : G₁ × G₂) (m : W ⊗[k] W') :
    TensorProduct.lift Φ.flip (outer A B p m) = τ p (TensorProduct.lift Φ.flip m) := by
  induction m with
  | tmul x y =>
    rw [outer_tmul, TensorProduct.lift.tmul, TensorProduct.lift.tmul, LinearMap.flip_apply,
      LinearMap.flip_apply, hΦeq, homRep_apply, hΦ y p.1 x, rep_one_mul]
  | add m m' h h' => simp only [map_add, h, h']

end Hom

variable {k G₁ G₂ : Type*} [Field k] [Group G₁] [Group G₂]

theorem exists_outer_equiv {ι₁ ι₂ : Type*} {W₁ : ι₁ → Type u} {W₂ : ι₂ → Type u}
    [∀ a, AddCommGroup (W₁ a)] [∀ a, Module k (W₁ a)] [∀ a, FiniteDimensional k (W₁ a)]
    [∀ b, AddCommGroup (W₂ b)] [∀ b, Module k (W₂ b)] [∀ b, FiniteDimensional k (W₂ b)]
    (A : ∀ a, Representation k G₁ (W₁ a)) (hA : ∀ a, AbsIrr (A a))
    (B : ∀ b, Representation k G₂ (W₂ b)) (hB : ∀ b, AbsIrr (B b))
    (hAc : ∀ (W : Type u) [AddCommGroup W] [Module k W] [FiniteDimensional k W]
      (σ : Representation k G₁ W), σ.IsIrreducible → ∃ a, Nonempty (σ.Equiv (A a)))
    (hBc : ∀ (W : Type u) [AddCommGroup W] [Module k W] [FiniteDimensional k W]
      (σ : Representation k G₂ W), σ.IsIrreducible → ∃ b, Nonempty (σ.Equiv (B b)))
    {U : Type u} [AddCommGroup U] [Module k U] [FiniteDimensional k U]
    (τ : Representation k (G₁ × G₂) U) (hτ : τ.IsIrreducible) :
    ∃ a b, Nonempty (τ.Equiv (outer (A a) (B b))) := by
  have hnt := ((isIrreducible_iff τ).1 hτ).1
  let τ₁ := τ.comp (MonoidHom.inl G₁ G₂)
  obtain ⟨U₁, -, hU₁, hU₁0, hU₁min⟩ := exists_minimal τ₁ (U₀ := ⊤)
    (fun _ _ _ => Submodule.mem_top) top_ne_bot
  obtain ⟨a, ⟨e₁⟩⟩ := hAc _ _ (isIrreducible_subrepOf hU₁ hU₁0 hU₁min)
  have := (hA a).1
  let φ₀ : W₁ a →ₗ[k] U := U₁.subtype ∘ₗ e₁.symm.toLinearEquiv.toLinearMap
  have hφ₀ : φ₀ ∈ homSpace τ (A a) := fun g x => by
    change ((e₁.symm (A a g x) : U₁) : U) = τ (g, 1) ((e₁.symm x : U₁) : U)
    rw [PairedTensorOrbits.Equiv.map_apply e₁.symm g x]
    rfl
  have hφ₀0 : φ₀ ≠ 0 := by
    obtain ⟨x, hx⟩ := exists_ne (0 : W₁ a)
    intro h
    have h1 := LinearMap.congr_fun h x
    change ((e₁.symm x : U₁) : U) = 0 at h1
    exact hx (e₁.symm.toLinearEquiv.map_eq_zero_iff.1 (Subtype.ext h1))
  have hH0 : homSpace τ (A a) ≠ ⊥ := fun h => hφ₀0 ((Submodule.mem_bot k).1 (h ▸ hφ₀))
  obtain ⟨Y, hYH, hY, hY0, hYmin⟩ :=
    exists_minimal (homRep (W₁ a) τ) (isInv_homSpace τ (A a)) hH0
  obtain ⟨b, ⟨e₂⟩⟩ := hBc _ _ (isIrreducible_subrepOf hY hY0 hYmin)
  have := (hB b).1
  let Φ : W₂ b →ₗ[k] W₁ a →ₗ[k] U := Y.subtype ∘ₗ e₂.symm.toLinearEquiv.toLinearMap
  let ev : W₁ a ⊗[k] W₂ b →ₗ[k] U := TensorProduct.lift Φ.flip
  have hev : ∀ x y, ev (x ⊗ₜ y) = ((e₂.symm y : Y) : W₁ a →ₗ[k] U) x := fun x y => rfl
  have hevG : ∀ p m, ev (outer (A a) (B b) p m) = τ p (ev m) :=
    lift_flip_outer τ (A a) (B b) Φ (fun y => hYH (e₂.symm y).2) fun h y => by
      change ((e₂.symm (B b h y) : Y) : W₁ a →ₗ[k] U) = _
      rw [PairedTensorOrbits.Equiv.map_apply e₂.symm h y]
      rfl
  have hev0 : ev ≠ 0 := by
    obtain ⟨y, hy⟩ := exists_ne (0 : W₂ b)
    have hψ : ((e₂.symm y : Y) : W₁ a →ₗ[k] U) ≠ 0 := fun h =>
      hy (e₂.symm.toLinearEquiv.map_eq_zero_iff.1 (Subtype.ext h))
    obtain ⟨x, hx⟩ : ∃ x, ((e₂.symm y : Y) : W₁ a →ₗ[k] U) x ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hψ (LinearMap.ext hcon)
    intro h
    exact hx ((hev x y).symm.trans (LinearMap.congr_fun h _))
  exact ⟨a, b, nonempty_equiv_of_ne_zero hτ ((hA a).outer (hB b)).isIrreducible ev hevG hev0⟩

end CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb
