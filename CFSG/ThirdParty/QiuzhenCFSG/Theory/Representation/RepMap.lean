module

public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.Algebra.Module.NatInt

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.SubrepresentationLattice

namespace CFSG
end CFSG
open CFSG

open Function
open scoped MonoidAlgebra

namespace CFSG.Theory.Representation

open _root_.Representation

/-- Bundled intertwining maps between two representations. -/
public abbrev RepMap {F G V W : Type*} [Semiring F] [Monoid G] [AddCommMonoid V]
    [AddCommMonoid W] [Module F V] [Module F W]
    (ρ : Representation F G V) (σ : Representation F G W) : Type _ :=
  IntertwiningMap ρ σ
/-- Notation for bundled intertwining maps between representations. -/
notation:25 ρ " →ₗ " σ:0 => RepMap ρ σ

namespace RepMap

variable {F G V W : Type*} [CommRing F] [Monoid G] [AddCommMonoid V] [AddCommMonoid W]
  [Module F V] [Module F W] (ρ : Representation F G V) (σ : Representation F G W)

public instance : FunLike (RepMap ρ σ) V W := IntertwiningMap.instFunLike _ _
public instance : Zero (RepMap ρ σ) := IntertwiningMap.instZero _ _
public instance : Add (RepMap ρ σ) := IntertwiningMap.instAdd _ _
public instance : SMul F (RepMap ρ σ) := IntertwiningMap.instSMul _ _
public instance : SMul ℕ (RepMap ρ σ) := IntertwiningMap.instSMulNat _ _
public instance instAddCommMonoid : AddCommMonoid (RepMap ρ σ) :=
  IntertwiningMap.instAddCommMonoid _ _
public instance : Module F (RepMap ρ σ) := IntertwiningMap.instModule _ _


@[simp]
public lemma coe_zero : ((0 : RepMap ρ σ) : V → W) = 0 := rfl

@[simp]
public lemma coe_add (f g : RepMap ρ σ) :
    ((f + g : RepMap ρ σ) : V → W) = f + g := rfl

@[simp]
public lemma coe_smul (a : F) (f : RepMap ρ σ) :
    ((a • f : RepMap ρ σ) : V → W) = a • f := rfl

@[simp]
public lemma coe_nsmul (n : ℕ) (f : RepMap ρ σ) :
    ((n • f : RepMap ρ σ) : V → W) = n • f := rfl


/-- Identification of intertwining maps with linear maps on the corresponding `F[G]`-modules. -/
@[expose]
public def equivLinearMapAsModule : RepMap ρ σ ≃ₗ[F] ρ.asModule →ₗ[F[G]] σ.asModule :=
  IntertwiningMap.equivLinearMapAsModule _ _

variable {ρ σ}

@[simp]
public theorem coe_toLinearMap (f : ρ →ₗ σ) : ⇑f.toLinearMap = f := rfl

@[simp]
public theorem coe_toAddHom (f : ρ →ₗ σ) : ⇑f.toAddHom = f := rfl

@[simp]
public theorem toFun_eq_coe {f : ρ →ₗ σ} : f.toFun = (f : V → W) := rfl

@[ext]
public theorem ext {f g : ρ →ₗ σ} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- A copy of an intertwining map with a prescribed function field. -/
@[expose]
public protected def copy (f : ρ →ₗ σ) (f' : V → W) (h : f' = ⇑f) : ρ →ₗ σ where
  toFun := f'
  map_add' := h.symm ▸ f.map_add'
  map_smul' := h.symm ▸ f.map_smul'
  isIntertwining' := h.symm ▸ f.isIntertwining'

@[simp]
public theorem coe_copy (f : ρ →ₗ σ) (f' : V → W) (h : f' = ⇑f) : ⇑(f.copy f' h) = f' :=
  by rfl


/-- Build an intertwining map from a linear map commuting with the actions. -/
@[expose]
public def mk (toLinearMap : V →ₗ[F] W) (isIntertwining : ∀ (g : G), toLinearMap ∘ₗ ρ g = σ g ∘ₗ toLinearMap) : RepMap ρ σ :=
  IntertwiningMap.mk toLinearMap isIntertwining

@[simp]
public theorem coe_mk (f : V →ₗ[F] W) (h) :
    ((.mk f h : ρ →ₗ σ) : V → W) = f :=
  by rfl

@[simp]
public theorem coe_linearMap_mk (f : V →ₗ[F] W) (h) :
    (.mk f h : ρ →ₗ σ).toLinearMap = f :=
  by rfl

public theorem toLinearMap_injective (f g : ρ →ₗ σ)
    (h : f.toLinearMap = g.toLinearMap) : f = g := by
  apply DFunLike.ext
  exact fun m ↦  DFunLike.congr_fun h m

/-- The identity intertwining map of a representation. -/
@[expose]
public noncomputable def id: ρ →ₗ ρ := IntertwiningMap.id _

@[simp]
public lemma id_apply (v : V) : IntertwiningMap.id ρ v = v := rfl

@[simp, norm_cast]
public theorem id_coe : (RepMap.id (ρ := ρ) : V → V) = _root_.id :=
  rfl

/-- Multiplication by a central group element as an intertwining endomorphism. -/
@[expose]
public def centralMul (g : G) (hg : g ∈ Submonoid.center G) : ρ →ₗ ρ :=
  IntertwiningMap.centralMul ρ g hg

variable {F G V W : Type*} [CommRing F] [Monoid G] [AddCommMonoid V] [AddCommMonoid W]
  [Module F V] [Module F W]
  {ρ : Representation F G V} {σ : Representation F G W}
  {f : ρ →ₗ σ} {g : ρ →ₗ σ}

public theorem coe_injective : Function.Injective (DFunLike.coe : (ρ →ₗ σ) → _) :=
  DFunLike.coe_injective

public protected theorem congr_arg {x x' : V} : x = x' → f x = f x' :=
  DFunLike.congr_arg f

public protected theorem congr_fun (h : f = g) (x : V) : f x = g x :=
  DFunLike.congr_fun h x

variable (f g)

@[simp]
public protected theorem map_add (x y : V) : f (x + y) = f x + f y :=
  map_add f.toLinearMap x y

@[simp]
public protected theorem map_zero : f 0 = 0 :=
  map_zero f.toLinearMap

@[simp]
public protected theorem map_smul (c : F) (x : V) : f (c • x) = c • f x :=
  map_smul f.toLinearMap c x

@[simp]
public protected theorem map_eq_zero_iff (h : Function.Injective f) {x : V} :
    f x = 0 ↔ x = 0 :=
  _root_.map_eq_zero_iff f.toLinearMap h

variable {F G V₁ V₂ V₃: Type*} [CommRing F] [Monoid G] [AddCommMonoid V₁]
  [AddCommMonoid V₂] [AddCommMonoid V₃] [Module F V₁] [Module F V₂] [Module F V₃]
  {ρ₁ : Representation F G V₁} {ρ₂ : Representation F G V₂} {ρ₃ : Representation F G V₃}
  (f : ρ₂ →ₗ ρ₃) (f' : ρ₂ →ₗ ρ₃) (g : ρ₁ →ₗ ρ₂) (g' : ρ₁ →ₗ ρ₂)

/-- Composition of intertwining maps. -/
@[expose]
public def comp : ρ₁ →ₗ ρ₃ := {
  toLinearMap := f.toLinearMap.comp g.toLinearMap
  isIntertwining' := fun h => by
    ext
    simp only [LinearMap.coe_comp, Function.comp_apply, IntertwiningMap.toLinearMap_apply]
    rw [g.isIntertwining, f.isIntertwining]
}

@[simp, norm_cast]
public theorem coe_comp : (f.comp g : V₁ → V₃) = f ∘ g :=
  rfl

@[simp]
public theorem comp_id : f.comp id = f :=
  rfl

@[simp]
public theorem id_comp : id.comp f = f :=
  rfl

public theorem comp_apply (v : V₁) : f.comp g v = f (g v) :=
  rfl

public theorem comp_assoc
    {V₀ : Type*} [AddCommMonoid V₀] [Module F V₀]
    {ρ₀ : Representation F G V₀} (h : ρ₀ →ₗ ρ₁) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

public lemma _root_.Function.Surjective.injective_RepMapComp_right (hg : Surjective g) :
    Injective fun f : ρ₂ →ₗ ρ₃ ↦ f.comp g :=
  fun _ _ h ↦ ext <| hg.forall.2 (RepMap.ext_iff.1 h)

@[simp]
public theorem cancel_right (hg : Surjective g) : f.comp g = f'.comp g ↔ f = f' :=
  hg.injective_RepMapComp_right.eq_iff

public lemma _root_.Function.Injective.injective_RepMapComp_left (hf : Injective f) :
    Injective fun g : ρ₁ →ₗ ρ₂ ↦ f.comp g :=
  fun g₁ g₂ (h : f.comp g₁ = f.comp g₂) ↦ ext fun x ↦ hf <| by rw [← comp_apply, h, comp_apply]


@[simp]
public theorem cancel_left (hf : Injective f) : f.comp g = f.comp g' ↔ g = g' :=
  hf.injective_RepMapComp_left.eq_iff

variable {F G V W : Type*} [CommRing F] [Monoid G] [AddCommMonoid V] [AddCommMonoid W]
  [Module F V] [Module F W] (ρ : Representation F G V) (σ : Representation F G W)

set_option backward.isDefEq.respectTransparency false in
/-- Construct an inverse intertwining map from two-sided inverse data. -/
@[expose]
public def inverse (f : ρ →ₗ σ) (g : W → V) (h₁ : LeftInverse g f) (h₂ : RightInverse g f) :
    σ →ₗ ρ := by
  dsimp [LeftInverse, Function.RightInverse] at h₁ h₂
  exact {
      toFun := g
      map_add' := fun x y ↦ by
        rw [← h₁ (g (x + y)), ← h₁ (g x + g y)]
        simp only [h₂, RepMap.map_add]
      map_smul' := fun a b ↦ by
        rw [← h₁ (g (a • b)), RingHom.id_apply, ← h₁ (a • g b)]
        simp only [h₂, RepMap.map_smul]
      isIntertwining' := fun h ↦ by
        ext v
        simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply]
        rw [← h₁ (g ((σ h) v)), ← h₁ ((ρ h) (g v)), h₂, (f.isIntertwining) h (g v), h₂]
    }

section

variable (f : ρ →ₗ σ) (g : σ →ₗ ρ) (h : g.comp f = .id)

include h


end

variable {F G V W : Type*} [CommRing F] [Monoid G] [AddCommGroup V] [AddCommGroup W]
  [Module F V] [Module F W] (ρ : Representation F G V) (σ : Representation F G W)
variable (f : ρ →ₗ σ)

@[simp]
public protected theorem map_neg (x : V) : f (-x) = -f x :=
  map_neg f.toLinearMap x

@[simp]
public protected theorem map_sub (x y : V) : f (x - y) = f x - f y :=
  map_sub f.toLinearMap x y

@[simp]
public theorem smul_apply (a : F) (f : ρ →ₗ σ) (x : V) : (a • f) x = a • f x :=
  rfl

@[simp]
public theorem zero_apply (x : V) : (0 : ρ →ₗ σ) x = 0 :=
  rfl

@[simp]
public theorem comp_zero : f.comp (0 : ρ →ₗ ρ) = 0 :=
  ext fun c ↦ by rw [comp_apply, zero_apply, zero_apply, RepMap.map_zero]

@[simp]
public theorem zero_comp : (0 : σ →ₗ σ).comp f = 0 :=
  rfl

public instance : Inhabited (ρ →ₗ σ) :=
  ⟨0⟩

@[simp]
public theorem default_def : (default : ρ →ₗ σ) = 0 :=
  rfl

public instance uniqueOfLeft [Subsingleton V] : Unique (ρ →ₗ σ) :=
  { (inferInstance : (Inhabited (ρ →ₗ σ))) with
    uniq := fun f => ext fun x => by
      rw [Subsingleton.elim x 0, RepMap.map_zero, RepMap.map_zero] }

public instance uniqueOfRight [Subsingleton W] : Unique (ρ →ₗ σ) :=
  coe_injective.unique

variable {f}

public theorem ne_zero_of_injective [Nontrivial V] (hf : Injective f) : f ≠ 0 :=
  have ⟨x, ne⟩ := exists_ne (0 : V)
  fun h ↦ hf.ne ne <| by simp [h]


@[simp]
public theorem add_apply (f g : ρ →ₗ σ) (x : V) : (f + g) x = f x + g x :=
  rfl

public theorem add_comp (f : ρ₁ →ₗ ρ₂) (g h : ρ₂ →ₗ ρ₃) :
    (h + g).comp f = h.comp f + g.comp f :=
  rfl

public theorem comp_add (f g : ρ₁ →ₗ ρ₂) (h : ρ₂ →ₗ ρ₃) :
    h.comp (f + g) = h.comp f + h.comp g :=
  ext fun _ ↦ h.map_add _ _

variable {V₁ V₂ V₃ : Type*} [AddCommGroup V₁] [AddCommGroup V₂] [AddCommGroup V₃]
  [Module F V₁] [Module F V₂] [Module F V₃]
  (ρ₁ : Representation F G V₁) (ρ₂ : Representation F G V₂) (ρ₃ : Representation F G V₃)


set_option backward.isDefEq.respectTransparency false in
public instance : Neg (ρ →ₗ σ) :=
  ⟨fun f ↦
    { toFun := -f
      map_add' := by simp [add_comm]
      map_smul' := by simp
      isIntertwining' := fun h ↦ by
        ext v
        simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply,
          Pi.neg_apply, map_neg, neg_inj]
        rw [f.isIntertwining] }⟩

@[simp]
public theorem neg_apply (f : ρ →ₗ σ) (x : V) : (-f) x = -f x :=
  rfl

@[simp]
public theorem neg_comp (f : ρ₁ →ₗ ρ₂) (g : ρ₂ →ₗ ρ₃) : (-g).comp f = -g.comp f :=
  rfl

@[simp]
public theorem comp_neg (f : ρ₁ →ₗ ρ₂) (g : ρ₂ →ₗ ρ₃) : g.comp (-f) = -g.comp f :=
  ext fun _ ↦ by simp only [coe_comp, Function.comp_apply, neg_apply, RepMap.map_neg]

set_option backward.isDefEq.respectTransparency false in
public instance : Sub (ρ →ₗ σ) :=
  ⟨fun f g ↦
    { toFun := f - g
      map_add' := fun x y ↦ by
        simp only [Pi.sub_apply, RepMap.map_add]
        grind
      map_smul' := fun r x ↦ by simp [Pi.sub_apply, smul_sub]
      isIntertwining' := fun h ↦ by
        ext v
        simp only [LinearMap.coe_comp, LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, Pi.sub_apply, f.isIntertwining, g.isIntertwining, map_sub] }⟩

@[simp]
public theorem sub_apply (f g : ρ →ₗ σ) (x : V) : (f - g) x = f x - g x :=
  rfl


public instance zsmul : SMul ℤ (ρ₁ →ₗ ρ₂) where
  smul := fun n f ↦ RepMap.mk (n • f.toLinearMap) (fun h ↦ by ext v; simp [f.isIntertwining])

public instance addCommGroup : AddCommGroup (ρ →ₗ σ) :=
  DFunLike.coe_injective.addCommGroup _ rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl)
    (fun _ _ ↦ rfl) fun _ _ ↦ by rfl

/-- Evaluation at a vector as an additive monoid hom on intertwining maps. -/
@[simps, expose]
public def evalAddMonoidHom (a : V) : (ρ →ₗ σ) →+ W where
  toFun f := f a
  map_add' f h := RepMap.add_apply ρ σ f h a
  map_zero' := rfl

@[simp]
public theorem identityMapOfZeroModuleIsZero [Subsingleton V] : id (ρ := ρ) = 0 :=
  Subsingleton.eq_zero id

/-- The range of an intertwining map as a subrepresentation. -/
@[expose]
public def range : Subrepresentation σ := {
  toSubmodule := LinearMap.range f.toLinearMap
  apply_mem_toSubmodule g v h := by
    simp only [LinearMap.mem_range, IntertwiningMap.toLinearMap_apply] at h ⊢
    obtain ⟨y, hy⟩ := h
    use (ρ g) y
    rw [f.isIntertwining, hy]
}

variable {F G V W : Type*} [Field F] [Monoid G] [AddCommGroup V] [AddCommGroup W]
  [Module F V] [Module F W] {ρ : Representation F G V} {σ : Representation F G W}

public theorem _root_.Representation.eq_bot_iff {p : Subrepresentation ρ} :
    p = ⊥ ↔ ∀ x ∈ p, x = 0 := by
  have : p.toSubmodule = ⊥ ↔ p = ⊥ := (StrictMono.apply_eq_bot_iff fun ⦃a b⦄ a_1 ↦ a_1)
  rw [← this, Submodule.eq_bot_iff]
  rfl

public theorem _root_.Representation.eq_top_iff' {p : Subrepresentation ρ} :
    p = ⊤ ↔ ∀ x, x ∈ p := by
  have : p.toSubmodule = ⊤ ↔ p = ⊤ := (StrictMono.apply_eq_top_iff fun ⦃a b⦄ a_1 ↦ a_1)
  rw [← this, Submodule.eq_top_iff']
  rfl

public theorem irreducible_of_inj {f : ρ →ₗ σ} [Nontrivial V] [inst : IsIrreducible σ] (h : Function.Injective f) : IsIrreducible ρ := by
  unfold IsIrreducible at inst ⊢
  rw [isSimpleOrder_iff_isAtom_top] at inst ⊢
  unfold IsAtom at inst ⊢
  contrapose! inst
  obtain ⟨a, ha1, ha2⟩ := inst top_ne_bot
  let b : Subrepresentation σ := {
    toSubmodule := a.toSubmodule.map f.toLinearMap
    apply_mem_toSubmodule g v he := by
      simp only [Submodule.mem_map, IntertwiningMap.toLinearMap_apply] at ⊢ he
      obtain ⟨c, hc1, hc2⟩ := he
      exact ⟨ρ g c, a.apply_mem_toSubmodule g hc1, by rw [f.isIntertwining, hc2]⟩
  }
  refine fun _ ↦ ⟨b, ?_, ?_⟩
  · contrapose ha1
    rw [not_lt_top_iff, Representation.eq_top_iff'] at ha1 ⊢
    intro v
    have : f v ∈ Submodule.map f.toLinearMap a.toSubmodule := ha1 (f v)
    obtain ⟨x, hx1, hx2⟩ := Submodule.mem_map.mp this
    rw [← h hx2]
    exact hx1
  · contrapose ha2
    rw [Representation.eq_bot_iff] at ⊢ ha2
    exact fun v hv ↦ h (RepMap.map_zero f ▸ ha2 (f v) (Submodule.mem_map_of_mem hv))

end RepMap
