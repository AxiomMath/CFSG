module

public import CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb.ProdIrr
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesSplit
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesFlip
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesInvolution

public noncomputable section

namespace CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb

open Module
open scoped MatrixGroups TensorProduct
open CFSG.QuasithinUnique.Setup.SL2Modules (frobTensor frobTensor_isIrreducible
  frobTensor_classification frobTensor_nonisomorphic finrank_frobTensor commutant_scalar)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.PairedTensorOrbits (AbsIrr AbsIrr.of_isIrreducible outer
  outer_tmul exists_minimal isIrreducible_subrepOf isIrreducible_iff isIrreducible_comp_iff
  equivOfCompSymm finiteDimensional_of_isIrreducible)

universe u

section Group

variable (F : Type u) [Field F]

abbrev Cube : Type u := Fin 3 → SL(2, F)

@[expose] def slot (s : Fin 3) : SL(2, F) →* Cube F :=
  MonoidHom.mulSingle (fun _ : Fin 3 => SL(2, F)) s

@[expose] def cubeEquiv : Cube F ≃* SL(2, F) × (SL(2, F) × SL(2, F)) where
  toFun g := (g 0, (g 1, g 2))
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv g := by
    funext i
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
  right_inv p := rfl
  map_mul' g h := rfl

variable {F}

theorem slot_apply_self (s : Fin 3) (g : SL(2, F)) : slot F s g s = g :=
  Pi.mulSingle_eq_same (M := fun _ : Fin 3 => SL(2, F)) s g

theorem slot_apply_of_ne {s t : Fin 3} (h : t ≠ s) (g : SL(2, F)) : slot F s g t = 1 :=
  Pi.mulSingle_eq_of_ne (M := fun _ : Fin 3 => SL(2, F)) h g

end Group

abbrev IsLabel (n : ℕ) (J : Fin 3 → Finset ℕ) : Prop :=
  ∀ s, ∀ i ∈ J s, i < n

section CubeRep

variable (F : Type u) [Field F]

abbrev CubeSpace (J : Fin 3 → Finset ℕ) : Type u :=
  ((J 0 → Fin 2) → F) ⊗[F] (((J 1 → Fin 2) → F) ⊗[F] ((J 2 → Fin 2) → F))

variable {F}

theorem finrank_cubeRep (J : Fin 3 → Finset ℕ) :
    finrank F (CubeSpace F J) = 2 ^ ((J 0).card + (J 1).card + (J 2).card) := by
  rw [Module.finrank_tensorProduct, Module.finrank_tensorProduct, finrank_frobTensor,
    finrank_frobTensor, finrank_frobTensor, pow_add, pow_add, mul_assoc]

@[expose] def cubeSwapTwo (J : Fin 3 → Finset ℕ) :
    CubeSpace F J ≃ₗ[F] ((J 2 → Fin 2) → F) ⊗[F] (((J 0 → Fin 2) → F) ⊗[F] ((J 1 → Fin 2) → F)) :=
  (TensorProduct.assoc F _ _ _).symm ≪≫ₗ TensorProduct.comm F _ _

theorem cubeSwapTwo_tmul (J : Fin 3 → Finset ℕ) (x : (J 0 → Fin 2) → F) (y : (J 1 → Fin 2) → F)
    (z : (J 2 → Fin 2) → F) : cubeSwapTwo J (x ⊗ₜ (y ⊗ₜ z)) = z ⊗ₜ (x ⊗ₜ y) :=
  rfl

variable (F) [CharP F 2]

@[expose] def cubeRep (J : Fin 3 → Finset ℕ) : Representation F (Cube F) (CubeSpace F J) :=
  (outer (frobTensor F F (J 0)) (outer (frobTensor F F (J 1)) (frobTensor F F (J 2)))).comp
    (cubeEquiv F).toMonoidHom

variable {F}

theorem cubeRep_apply (J : Fin 3 → Finset ℕ) (g : Cube F) :
    cubeRep F J g = TensorProduct.map (frobTensor F F (J 0) (g 0))
      (TensorProduct.map (frobTensor F F (J 1) (g 1)) (frobTensor F F (J 2) (g 2))) :=
  rfl

theorem cubeRep_tmul (J : Fin 3 → Finset ℕ) (g : Cube F) (x : (J 0 → Fin 2) → F)
    (y : (J 1 → Fin 2) → F) (z : (J 2 → Fin 2) → F) :
    cubeRep F J g (x ⊗ₜ (y ⊗ₜ z)) = frobTensor F F (J 0) (g 0) x ⊗ₜ
      (frobTensor F F (J 1) (g 1) y ⊗ₜ frobTensor F F (J 2) (g 2) z) :=
  rfl

theorem cubeRep_slot_zero (J : Fin 3 → Finset ℕ) (g : SL(2, F)) :
    cubeRep F J (slot F 0 g) = TensorProduct.map (frobTensor F F (J 0) g) LinearMap.id := by
  refine TensorProduct.ext_threefold' fun x y z => ?_
  rw [cubeRep_tmul, slot_apply_self, slot_apply_of_ne (show (1 : Fin 3) ≠ 0 by decide),
    slot_apply_of_ne (show (2 : Fin 3) ≠ 0 by decide), map_one, map_one, Module.End.one_apply,
    Module.End.one_apply, TensorProduct.map_tmul, LinearMap.id_apply]

theorem leftComm_cubeRep_slot_one (J : Fin 3 → Finset ℕ) (g : SL(2, F)) (v : CubeSpace F J) :
    TensorProduct.leftComm F _ _ _ (cubeRep F J (slot F 1 g) v) =
      TensorProduct.map (frobTensor F F (J 1) g) LinearMap.id
        (TensorProduct.leftComm F _ _ _ v) := by
  have h := TensorProduct.ext_threefold'
    (g := (TensorProduct.leftComm F _ _ _).toLinearMap ∘ₗ cubeRep F J (slot F 1 g))
    (h := TensorProduct.map (frobTensor F F (J 1) g) LinearMap.id ∘ₗ
      (TensorProduct.leftComm F _ _ _).toLinearMap) fun x y z => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, cubeRep_tmul, slot_apply_self,
      slot_apply_of_ne (show (0 : Fin 3) ≠ 1 by decide),
      slot_apply_of_ne (show (2 : Fin 3) ≠ 1 by decide), map_one, map_one, Module.End.one_apply,
      Module.End.one_apply, LinearEquiv.coe_toLinearMap, TensorProduct.leftComm_tmul,
      TensorProduct.leftComm_tmul, TensorProduct.map_tmul, LinearMap.id_apply]
  exact LinearMap.congr_fun h v

theorem cubeSwapTwo_cubeRep_slot_two (J : Fin 3 → Finset ℕ) (g : SL(2, F)) (v : CubeSpace F J) :
    cubeSwapTwo J (cubeRep F J (slot F 2 g) v) =
      TensorProduct.map (frobTensor F F (J 2) g) LinearMap.id (cubeSwapTwo J v) := by
  have h := TensorProduct.ext_threefold'
    (g := (cubeSwapTwo J).toLinearMap ∘ₗ cubeRep F J (slot F 2 g))
    (h := TensorProduct.map (frobTensor F F (J 2) g) LinearMap.id ∘ₗ (cubeSwapTwo J).toLinearMap)
    fun x y z => by
    rw [LinearMap.comp_apply, LinearMap.comp_apply, cubeRep_tmul, slot_apply_self,
      slot_apply_of_ne (show (0 : Fin 3) ≠ 2 by decide),
      slot_apply_of_ne (show (1 : Fin 3) ≠ 2 by decide), map_one, map_one, Module.End.one_apply,
      Module.End.one_apply, LinearEquiv.coe_toLinearMap, cubeSwapTwo_tmul,
      cubeSwapTwo_tmul, TensorProduct.map_tmul, LinearMap.id_apply]
  exact LinearMap.congr_fun h v

end CubeRep

section Irreducible

variable {F : Type u} [Field F] [Fintype F] [CharP F 2] {n : ℕ}

theorem frobTensor_absIrr (hF : Fintype.card F = 2 ^ n) {J : Finset ℕ} (hJ : ∀ i ∈ J, i < n) :
    AbsIrr (frobTensor F F J) :=
  AbsIrr.of_isIrreducible (frobTensor_isIrreducible hF hJ) fun f hf =>
    commutant_scalar hF (fun i : J => (i : ℕ)) Subtype.val_injective (fun i => hJ i i.2) f
      fun g => LinearMap.ext fun x => hf g x

theorem cubeRep_absIrr (hF : Fintype.card F = 2 ^ n) {J : Fin 3 → Finset ℕ} (hJ : IsLabel n J) :
    AbsIrr (cubeRep F J) := by
  have h := (frobTensor_absIrr hF (hJ 0)).outer
    ((frobTensor_absIrr hF (hJ 1)).outer (frobTensor_absIrr hF (hJ 2)))
  refine ⟨h.1, ?_⟩
  have hr : Set.range (cubeRep F J) = Set.range
      (outer (frobTensor F F (J 0)) (outer (frobTensor F F (J 1)) (frobTensor F F (J 2)))) :=
    (cubeEquiv F).surjective.range_comp
      (outer (frobTensor F F (J 0)) (outer (frobTensor F F (J 1)) (frobTensor F F (J 2))))
  rw [hr]
  exact h.2

theorem cubeRep_isIrreducible (hF : Fintype.card F = 2 ^ n) {J : Fin 3 → Finset ℕ}
    (hJ : IsLabel n J) : (cubeRep F J).IsIrreducible :=
  (cubeRep_absIrr hF hJ).isIrreducible

end Irreducible

section Classification

variable {F : Type u} [Field F] [Fintype F] [CharP F 2] {n : ℕ}

theorem cube_classification (hF : Fintype.card F = 2 ^ n) {U : Type u} [AddCommGroup U]
    [Module F U] (σ : Representation F (Cube F) U) (hσ : σ.IsIrreducible) :
    ∃ J, IsLabel n J ∧ Nonempty (σ.Equiv (cubeRep F J)) := by
  have : FiniteDimensional F U := finiteDimensional_of_isIrreducible hσ
  let L := {J : Finset ℕ // ∀ i ∈ J, i < n}
  have hA : ∀ a : L, AbsIrr (frobTensor F F a.1) := fun a => frobTensor_absIrr hF a.2
  have hAc : ∀ (W : Type u) [AddCommGroup W] [Module F W] [FiniteDimensional F W]
      (ρ : Representation F SL(2, F) W), ρ.IsIrreducible →
      ∃ a : L, Nonempty (ρ.Equiv (frobTensor F F a.1)) := by
    intro W _ _ _ ρ hρ
    obtain ⟨J, ⟨hJ, he⟩, -⟩ := frobTensor_classification hF ρ hρ
    exact ⟨⟨J, hJ⟩, he⟩
  have hBc : ∀ (W : Type u) [AddCommGroup W] [Module F W] [FiniteDimensional F W]
      (ρ : Representation F (SL(2, F) × SL(2, F)) W), ρ.IsIrreducible →
      ∃ b : L × L, Nonempty (ρ.Equiv (outer (frobTensor F F b.1.1) (frobTensor F F b.2.1))) := by
    intro W _ _ _ ρ hρ
    obtain ⟨a, b, he⟩ := exists_outer_equiv (W₁ := fun a : L => (a.1 → Fin 2) → F)
      (W₂ := fun a : L => (a.1 → Fin 2) → F) (fun a : L => frobTensor F F a.1) hA
      (fun a : L => frobTensor F F a.1) hA hAc hAc ρ hρ
    exact ⟨(a, b), he⟩
  obtain ⟨a, b, ⟨e⟩⟩ := exists_outer_equiv (W₁ := fun a : L => (a.1 → Fin 2) → F)
    (W₂ := fun b : L × L => ((b.1.1 → Fin 2) → F) ⊗[F] ((b.2.1 → Fin 2) → F))
    (fun a : L => frobTensor F F a.1) hA
    (fun b : L × L => outer (frobTensor F F b.1.1) (frobTensor F F b.2.1))
    (fun b => (hA b.1).outer (hA b.2)) hAc hBc (σ.comp (cubeEquiv F).symm.toMonoidHom)
    ((isIrreducible_comp_iff σ (cubeEquiv F).symm).2 hσ)
  refine ⟨![a.1, b.1.1, b.2.1], fun s => ?_, ⟨equivOfCompSymm (cubeEquiv F) e⟩⟩
  match s with
  | 0 => exact a.2
  | 1 => exact b.1.2
  | 2 => exact b.2.2

theorem cubeRep_slot_equiv (hF : Fintype.card F = 2 ^ n) {J : Fin 3 → Finset ℕ} (hJ : IsLabel n J)
    (s : Fin 3) {E : Type*} [AddCommGroup E] [Module F E] {σ : Representation F SL(2, F) E}
    (hσ : σ.IsIrreducible) (f : E →ₗ[F] CubeSpace F J)
    (hf : ∀ g v, f (σ g v) = cubeRep F J (slot F s g) (f v)) (hf0 : f ≠ 0) :
    Nonempty (σ.Equiv (frobTensor F F (J s))) := by
  have hρ : ∀ s, (frobTensor F F (J s)).IsIrreducible := fun s => frobTensor_isIrreducible hF (hJ s)
  match s with
  | 0 =>
    exact nonempty_equiv_of_tensorEquiv hσ (τ := (cubeRep F J).comp (slot F 0)) (hρ 0)
      (LinearEquiv.refl F _) (fun g v => LinearMap.congr_fun (cubeRep_slot_zero J g) v) f hf hf0
  | 1 =>
    exact nonempty_equiv_of_tensorEquiv hσ (τ := (cubeRep F J).comp (slot F 1)) (hρ 1)
      (TensorProduct.leftComm F _ _ _) (leftComm_cubeRep_slot_one J) f hf hf0
  | 2 =>
    exact nonempty_equiv_of_tensorEquiv hσ (τ := (cubeRep F J).comp (slot F 2)) (hρ 2)
      (cubeSwapTwo J) (cubeSwapTwo_cubeRep_slot_two J) f hf hf0

theorem cubeRep_injective (hF : Fintype.card F = 2 ^ n) {J J' : Fin 3 → Finset ℕ}
    (hJ : IsLabel n J) (hJ' : IsLabel n J') (φ : (cubeRep F J).Equiv (cubeRep F J')) : J = J' := by
  funext s
  have := (cubeRep_absIrr hF hJ).1
  obtain ⟨U, -, hU, hU0, hUmin⟩ := exists_minimal ((cubeRep F J).comp (slot F s)) (U₀ := ⊤)
    (fun _ _ _ => Submodule.mem_top) top_ne_bot
  have hirr := isIrreducible_subrepOf hU hU0 hUmin
  have hsub0 : U.subtype ≠ 0 := by
    obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    intro h
    exact hu0 (LinearMap.congr_fun h ⟨u, huU⟩)
  obtain ⟨e₁⟩ := cubeRep_slot_equiv hF hJ s hirr U.subtype (fun g v => rfl) hsub0
  obtain ⟨e₂⟩ := cubeRep_slot_equiv hF hJ' s hirr (φ.toLinearMap ∘ₗ U.subtype)
    (fun g v => PairedTensorOrbits.Equiv.map_apply φ (slot F s g) (v : CubeSpace F J))
    fun h => hsub0 (by
      ext v
      have h1 : φ (v : CubeSpace F J) = 0 := LinearMap.congr_fun h v
      exact φ.toLinearEquiv.map_eq_zero_iff.1 h1)
  exact frobTensor_nonisomorphic hF (hJ s) (hJ' s) (e₁.symm.trans e₂)

end Classification

end CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb
