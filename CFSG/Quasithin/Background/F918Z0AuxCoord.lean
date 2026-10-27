module

public import CFSG.Quasithin.Background.F918Z0Def
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

public section

namespace CFSG.Quasithin.MatModel

open scoped Matrix
open Module

variable {F : Type} [Field F] {I : Type} [AddCommGroup I] [Module F I] {d r : ℕ}

@[expose] noncomputable def toMat (b : Basis (Fin d) F I) :
    (Fin r → I) ≃+ Matrix (Fin d) (Fin r) F where
  toFun f := Matrix.of fun a j => b.equivFun (f j) a
  invFun M j := b.equivFun.symm fun a => M a j
  left_inv f := by
    funext j
    simp
  right_inv M := by
    ext a j
    exact congrFun (b.equivFun.apply_symm_apply fun a => M a j) a
  map_add' f g := by
    ext a j
    simp

theorem toMat_apply (b : Basis (Fin d) F I) (f : Fin r → I) (a : Fin d) (j : Fin r) :
    toMat b f a j = b.equivFun (f j) a :=
  rfl

theorem toMat_map (b : Basis (Fin d) F I) (u : Module.End F I) (f : Fin r → I) :
    toMat b (fun j => u (f j)) = LinearMap.toMatrix b b u * toMat b f := by
  ext a j
  have h := congrFun (LinearMap.toMatrix_mulVec_repr b b u (f j)) a
  rw [toMat_apply, Matrix.mul_apply]
  simpa [Matrix.mulVec, dotProduct, toMat_apply] using h.symm

theorem toMat_comb (b : Basis (Fin d) F I) (M : Matrix (Fin r) (Fin r) F) (f : Fin r → I) :
    toMat b (fun i => ∑ j, M i j • f j) = toMat b f * Mᵀ := by
  ext a i
  rw [toMat_apply, Matrix.mul_apply]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, toMat_apply,
    Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

section Coordinates

@[expose] noncomputable def repHom (b : Basis (Fin d) F I) :
    Module.End F I →* Matrix (Fin d) (Fin d) F where
  toFun := LinearMap.toMatrix b b
  map_one' := LinearMap.toMatrix_one b
  map_mul' := LinearMap.toMatrix_mul b

theorem equivFun_apply_map (b : Basis (Fin d) F I) (u : Module.End F I) (w : I) :
    b.equivFun (u w) = (LinearMap.toMatrix b b u).mulVec (b.equivFun w) := by
  simpa using (LinearMap.toMatrix_mulVec_repr b b u w).symm

variable {G : Type*} [Group G]

theorem irr_of_coords (b : Basis (Fin d) F I) (ρI : G →* Module.End F I)
    (hI : ∀ W : AddSubgroup I, (∀ g : G, ∀ w ∈ W, ρI g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (W : AddSubgroup (Fin d → F))
    (hW : ∀ g : G, ∀ w ∈ W, (LinearMap.toMatrix b b (ρI g)).mulVec w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  let W' : AddSubgroup I := W.comap (b.equivFun : I ≃ₗ[F] (Fin d → F)).toAddMonoidHom
  have hmem : ∀ w : I, w ∈ W' ↔ b.equivFun w ∈ W := fun w => Iff.rfl
  have hW' : ∀ g : G, ∀ w ∈ W', ρI g w ∈ W' := by
    intro g w hw
    rw [hmem, equivFun_apply_map]
    exact hW g _ ((hmem w).mp hw)
  rcases hI W' hW' with h | h
  · left
    rw [eq_bot_iff]
    intro w hw
    have h1 : b.equivFun.symm w ∈ W' := by
      rw [hmem, LinearEquiv.apply_symm_apply]
      exact hw
    rw [h, AddSubgroup.mem_bot] at h1
    rw [AddSubgroup.mem_bot, ← LinearEquiv.apply_symm_apply b.equivFun w, h1, map_zero]
  · right
    rw [eq_top_iff]
    intro w _
    have h1 : b.equivFun.symm w ∈ W' := by rw [h]; trivial
    rwa [hmem, LinearEquiv.apply_symm_apply] at h1

theorem comm_of_coords (b : Basis (Fin d) F I) (ρI : G →* Module.End F I)
    (hC : ∀ φ : I →+ I, (∀ (g : G) (w : I), φ (ρI g w) = ρI g (φ w)) →
      ∃ c : F, ∀ w, φ w = c • w)
    (φ : (Fin d → F) →+ (Fin d → F))
    (hφ : ∀ (g : G) (w : Fin d → F), φ ((LinearMap.toMatrix b b (ρI g)).mulVec w) =
      (LinearMap.toMatrix b b (ρI g)).mulVec (φ w)) :
    ∃ c : F, ∀ w, φ w = c • w := by
  let e : I ≃ₗ[F] (Fin d → F) := b.equivFun
  let φ' : I →+ I := e.symm.toAddMonoidHom.comp (φ.comp e.toAddMonoidHom)
  have hφ' : ∀ (g : G) (w : I), φ' (ρI g w) = ρI g (φ' w) := by
    intro g w
    apply e.injective
    have h1 : e (φ' (ρI g w)) = (LinearMap.toMatrix b b (ρI g)).mulVec (φ (e w)) := by
      change e (e.symm (φ (e (ρI g w)))) = _
      rw [LinearEquiv.apply_symm_apply]
      change φ (b.equivFun (ρI g w)) = _
      rw [equivFun_apply_map, hφ]
    have h2 : e (ρI g (φ' w)) = (LinearMap.toMatrix b b (ρI g)).mulVec (φ (e w)) := by
      change b.equivFun (ρI g (e.symm (φ (e w)))) = _
      rw [equivFun_apply_map]
      rw [show b.equivFun (e.symm (φ (e w))) = φ (e w) from e.apply_symm_apply _]
    rw [h1, h2]
  obtain ⟨c, hc⟩ := hC φ' hφ'
  refine ⟨c, fun w => ?_⟩
  have h3 : φ' (e.symm w) = e.symm (φ w) := by
    change e.symm (φ (e (e.symm w))) = _
    rw [LinearEquiv.apply_symm_apply]
  have h4 := hc (e.symm w)
  rw [h3] at h4
  calc φ w = e (e.symm (φ w)) := (e.apply_symm_apply _).symm
    _ = e (c • e.symm w) := by rw [h4]
    _ = c • w := by rw [map_smul, LinearEquiv.apply_symm_apply]

end Coordinates

section Assembly

variable {V : Type} [CommGroup V]

theorem invariant_sup_aut {D X : Subgroup (MulAut V)} {U : Subgroup V}
    (hD : ∀ g ∈ D, ∀ u ∈ U, g u ∈ U) (hX : ∀ g ∈ X, ∀ u ∈ U, g u ∈ U) :
    ∀ g ∈ D ⊔ X, ∀ u ∈ U, g u ∈ U := by
  intro g hg
  rw [Subgroup.sup_eq_closure] at hg
  induction hg using Subgroup.closure_induction'' with
  | mem g hg =>
    rcases hg with hg | hg
    · exact hD g hg
    · exact hX g hg
  | inv_mem g hg =>
    rcases hg with hg | hg
    · exact hD g⁻¹ (D.inv_mem hg)
    · exact hX g⁻¹ (X.inv_mem hg)
  | one => intro v hv; exact hv
  | mul g h _ _ ihg ihh => intro v hv; exact ihg _ (ihh v hv)

@[expose] def mulEquivOfAddEquiv {A B : Type*} [CommGroup A] [AddCommGroup B]
    (e : Additive A ≃+ B) : A ≃* Multiplicative B where
  toFun a := Multiplicative.ofAdd (e (Additive.ofMul a))
  invFun b := Additive.toMul (e.symm (Multiplicative.toAdd b))
  left_inv a := by simp
  right_inv b := by simp
  map_mul' a b := by
    rw [ofMul_mul, map_add, ofAdd_add]

structure IsDecomp {V : Type} [CommGroup V] (D X : Subgroup (MulAut V)) {F : Type} [Field F]
    {I : Type} [AddCommGroup I] [Module F I] {r : ℕ} (Φ : (Fin r → I) ≃+ Additive V)
    (ρI : ↥D →* Module.End F I) (σ : ↥X →* Matrix.GeneralLinearGroup (Fin r) F) : Prop where
  hρ : ∀ (g : ↥D) (f : Fin r → I),
    Φ (fun i => ρI g (f i)) = Additive.ofMul ((g : MulAut V) (Additive.toMul (Φ f)))
  hσ : ∀ (x : ↥X) (f : Fin r → I) (i : Fin r),
    Φ.symm (Additive.ofMul ((x : MulAut V) (Additive.toMul (Φ f)))) i =
      ∑ j, ((σ x : Matrix.GeneralLinearGroup (Fin r) F) : Matrix (Fin r) (Fin r) F) i j • f j
  hI : ∀ W : AddSubgroup I, (∀ g : ↥D, ∀ w ∈ W, ρI g w ∈ W) → W = ⊥ ∨ W = ⊤
  hC : ∀ φ : I →+ I, (∀ (g : ↥D) (w : I), φ (ρI g w) = ρI g (φ w)) →
    ∃ c : F, ∀ w, φ w = c • w

@[expose] def rowSub {F : Type} [Field F] {d r : ℕ}
    (β : V ≃* Multiplicative (Matrix (Fin d) (Fin r) F)) (W : Submodule F (Fin r → F)) :
    Subgroup V where
  carrier := {v | ∀ a : Fin d, Multiplicative.toAdd (β v) a ∈ W}
  one_mem' a := by
    rw [map_one, toAdd_one]
    exact W.zero_mem
  mul_mem' {u v} hu hv a := by
    rw [map_mul, toAdd_mul]
    exact W.add_mem (hu a) (hv a)
  inv_mem' {u} hu a := by
    rw [map_inv, toAdd_inv]
    exact W.neg_mem (hu a)

theorem mem_rowSub {F : Type} [Field F] {d r : ℕ}
    {β : V ≃* Multiplicative (Matrix (Fin d) (Fin r) F)} {W : Submodule F (Fin r → F)} {v : V} :
    v ∈ rowSub β W ↔ ∀ a : Fin d, Multiplicative.toAdd (β v) a ∈ W :=
  Iff.rfl

theorem row_mul {F : Type} [Field F] {d r : ℕ} (A : Matrix (Fin d) (Fin d) F)
    (M : Matrix (Fin d) (Fin r) F) (a : Fin d) : (A * M) a = ∑ c, A a c • M c := by
  funext j
  simp [Matrix.mul_apply, Finset.sum_apply]

theorem row_mul_transpose {F : Type} [Field F] {d r : ℕ} (M : Matrix (Fin d) (Fin r) F)
    (N : Matrix (Fin r) (Fin r) F) (a : Fin d) : (M * Nᵀ) a = N.mulVec (M a) := by
  funext i
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]

theorem exists_isMatModel {D X : Subgroup (MulAut V)} {F : Type} [Field F]
    {I : Type} [AddCommGroup I] [Module F I] {d r : ℕ} (b : Basis (Fin d) F I) (hd : 0 < d)
    {Φ : (Fin r → I) ≃+ Additive V} {ρI : ↥D →* Module.End F I}
    {σ : ↥X →* Matrix.GeneralLinearGroup (Fin r) F} (h : IsDecomp D X Φ ρI σ)
    (hirr : ∀ U : Subgroup V, (∀ g ∈ D ⊔ X, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤) :
    ∃ (β : V ≃* Multiplicative (Matrix (Fin d) (Fin r) F))
      (ρ : ↥D →* Matrix.GeneralLinearGroup (Fin d) F), IsMatModel D X β ρ σ := by
  let e : Additive V ≃+ Matrix (Fin d) (Fin r) F := Φ.symm.trans (toMat b)
  let β : V ≃* Multiplicative (Matrix (Fin d) (Fin r) F) := mulEquivOfAddEquiv e
  let ρ : ↥D →* Matrix.GeneralLinearGroup (Fin d) F := ((repHom b).comp ρI).toHomUnits
  have hρc : ∀ g : ↥D, ((ρ g : Matrix.GeneralLinearGroup (Fin d) F) :
      Matrix (Fin d) (Fin d) F) = LinearMap.toMatrix b b (ρI g) := fun g => rfl
  have hβ : ∀ v : V, Multiplicative.toAdd (β v) = toMat b (Φ.symm (Additive.ofMul v)) :=
    fun v => rfl
  have hD : ∀ (g : ↥D) (v : V), Φ.symm (Additive.ofMul ((g : MulAut V) v)) =
      fun i => ρI g (Φ.symm (Additive.ofMul v) i) := by
    intro g v
    apply Φ.injective
    have h1 := h.hρ g (Φ.symm (Additive.ofMul v))
    rw [AddEquiv.apply_symm_apply, toMul_ofMul] at h1
    rw [AddEquiv.apply_symm_apply]
    exact h1.symm
  have hX : ∀ (x : ↥X) (v : V), Φ.symm (Additive.ofMul ((x : MulAut V) v)) =
      fun i => ∑ j, ((σ x : Matrix.GeneralLinearGroup (Fin r) F) : Matrix (Fin r) (Fin r) F) i j •
        Φ.symm (Additive.ofMul v) j := by
    intro x v
    funext i
    have h1 := h.hσ x (Φ.symm (Additive.ofMul v)) i
    rwa [AddEquiv.apply_symm_apply, toMul_ofMul] at h1
  have hρβ : ∀ (g : ↥D) (v : V), β ((g : MulAut V) v) =
      Multiplicative.ofAdd (((ρ g : Matrix.GeneralLinearGroup (Fin d) F) :
        Matrix (Fin d) (Fin d) F) * Multiplicative.toAdd (β v)) := by
    intro g v
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd, hβ, hβ, hD, toMat_map, hρc]
  have hσβ : ∀ (x : ↥X) (v : V), β ((x : MulAut V) v) =
      Multiplicative.ofAdd (Multiplicative.toAdd (β v) *
        (((σ x : Matrix.GeneralLinearGroup (Fin r) F) : Matrix (Fin r) (Fin r) F))ᵀ) := by
    intro x v
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd, hβ, hβ, hX, toMat_comb]
  refine ⟨β, ρ, hρβ, hσβ, ?_, ?_, ?_⟩
  · intro W hW
    exact irr_of_coords b ρI h.hI W (fun g w hw => by simpa [hρc] using hW g w hw)
  · intro φ hφ
    exact comm_of_coords b ρI h.hC φ (fun g w => by simpa [hρc] using hφ g w)
  · intro W hW
    have hU : ∀ g ∈ D ⊔ X, ∀ u ∈ rowSub β W, g u ∈ rowSub β W := by
      apply invariant_sup_aut
      · intro g hg u hu a
        rw [mem_rowSub] at hu
        rw [hρβ ⟨g, hg⟩ u, toAdd_ofAdd, row_mul]
        exact W.sum_mem fun c _ => W.smul_mem _ (hu c)
      · intro g hg u hu a
        rw [mem_rowSub] at hu
        rw [hσβ ⟨g, hg⟩ u, toAdd_ofAdd, row_mul_transpose]
        exact hW ⟨g, hg⟩ _ (hu a)
    have hrow : ∀ w : Fin r → F, (Matrix.of fun _ : Fin d => w) =
        Multiplicative.toAdd (β (β.symm (Multiplicative.ofAdd (Matrix.of fun _ : Fin d => w)))) :=
      fun w => by rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]
    rcases hirr _ hU with h0 | h0
    · left
      rw [eq_bot_iff]
      intro w hw
      have hv : β.symm (Multiplicative.ofAdd (Matrix.of fun _ : Fin d => w)) ∈ rowSub β W := by
        intro a
        rw [← hrow]
        exact hw
      rw [h0, Subgroup.mem_bot] at hv
      have h1 : (Matrix.of fun _ : Fin d => w) = 0 := by
        have := congrArg (fun v => Multiplicative.toAdd (β v)) hv
        simpa [← hrow w] using this
      exact congrFun h1 ⟨0, hd⟩
    · right
      rw [eq_top_iff]
      intro w _
      have hv : β.symm (Multiplicative.ofAdd (Matrix.of fun _ : Fin d => w)) ∈ rowSub β W := by
        rw [h0]
        trivial
      have := hv ⟨0, hd⟩
      rw [← hrow] at this
      exact this

theorem hasMatModel_of_isDecomp {D X : Subgroup (MulAut V)} {F : Type} [Field F] [Finite F]
    [CharP F 2] {I : Type} [AddCommGroup I] [Module F I] [Module.Finite F I] [Nontrivial I]
    {r : ℕ} (hr : 0 < r) {Φ : (Fin r → I) ≃+ Additive V} {ρI : ↥D →* Module.End F I}
    {σ : ↥X →* Matrix.GeneralLinearGroup (Fin r) F} (h : IsDecomp D X Φ ρI σ)
    (hirr : ∀ U : Subgroup V, (∀ g ∈ D ⊔ X, ∀ u ∈ U, g u ∈ U) → U = ⊥ ∨ U = ⊤) :
    HasMatModel D X := by
  obtain ⟨β, ρ, hM⟩ := exists_isMatModel (Module.finBasis F I) Module.finrank_pos h hirr
  exact ⟨F, inferInstance, inferInstance, inferInstance, _, r, β, ρ, σ, Module.finrank_pos, hr,
    hM⟩

end Assembly

end CFSG.Quasithin.MatModel
