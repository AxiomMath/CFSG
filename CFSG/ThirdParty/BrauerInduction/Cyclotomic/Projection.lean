module

public import CFSG.ThirdParty.BrauerInduction.Cyclotomic.IntegralCharacterRing
public import CFSG.ThirdParty.BrauerInduction.Background.ClassFun.Character.Ring
public import CFSG.ThirdParty.BrauerInduction.Background.Fintype.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# Projection from cyclotomic to integral character coefficients

This file constructs Bernstein's additive coefficient projection and packages
its action on class functions.

First, `exists_projection_of_primitive` proves that a primitive element of a
finite free `ℤ`-module admits a `ℤ`-linear projection to `ℤ` sending that
element to `1`. Applied to `ClassFun.Lambda k G`, this yields a chosen additive
map `nu : Lambda k G →+ ℤ` with `nu 1 = 1`.

The auxiliary function `nu_ext` extends this projection to all of `k` by zero
outside `Lambda k G`. It is used only on arguments known to lie in the
cyclotomic coefficient ring, where it is additive and compatible with integer
scalars.

Finally, `nuStar` applies `nu_ext` to coordinates in an irreducible-character
basis. On functions with cyclotomic coordinates it is additive, `ℤ`-linear,
and fixes representation characters. The map `nuStarLinear` restricts this
construction to a linear map from
`ClassFun.IntegralCyclotomicCharacterRing k G` to
`ClassFun.CharacterRing k G`.
-/

namespace CFSG.BrauerInduction.Cyclotomic

/--
In a finitely generated free `ℤ`-module, every primitive element admits a
linear projection to `ℤ` sending it to `1`.

Here “primitive” means that if `v = m • x`, then `m` is a unit of `ℤ`.
-/
lemma exists_projection_of_primitive {M : Type*} [AddCommGroup M] [Module ℤ M]
    [Module.Free ℤ M] [Module.Finite ℤ M]
    (v : M) (h_prim : ∀ (m : ℤ) (x : M), m • x = v → IsUnit m) :
    ∃ ν : M →ₗ[ℤ] ℤ, ν v = 1 := by
  let eval_v : (M →ₗ[ℤ] ℤ) →ₗ[ℤ] ℤ := {
    toFun := fun f => f v
    map_add' := fun f g => rfl
    map_smul' := fun c f => rfl
  }
  let I := LinearMap.range eval_v
  haveI : Submodule.IsPrincipal I := inferInstance
  obtain ⟨d, hd⟩ : ∃ d, Submodule.span ℤ {d} = I :=
    ⟨Submodule.IsPrincipal.generator I, Submodule.IsPrincipal.span_singleton_generator I⟩
  let ι := Module.Free.ChooseBasisIndex ℤ M
  letI : Fintype ι := Module.Free.ChooseBasisIndex.fintype ℤ M
  let b := Module.Free.chooseBasis ℤ M
  have h_coord_in : ∀ i, b.coord i v ∈ I := by
    intro i
    exact LinearMap.mem_range.mpr ⟨b.coord i, rfl⟩
  have h_w : ∀ i, ∃ w_i : ℤ, b.coord i v = d * w_i := by
    intro i
    have h1 := h_coord_in i
    rw [← hd] at h1
    have h2 := Submodule.mem_span_singleton.mp h1
    obtain ⟨y, hy⟩ := h2
    use y
    rw [← hy, smul_eq_mul, mul_comm]
  choose w hw using h_w
  let W_repr : ι →₀ ℤ := ∑ i, Finsupp.single i (w i)
  let W := b.repr.symm W_repr
  have h_W_repr_i : ∀ i, W_repr i = w i := by
    intro i
    have h_eval : W_repr i = ∑ j, (Finsupp.single j (w j)) i := by
      exact Finsupp.finsetSum_apply Finset.univ (fun j => Finsupp.single j (w j)) i
    rw [h_eval]
    rw [Finset.sum_eq_single i]
    · exact Finsupp.single_eq_same
    · intro j _ hj
      exact Finsupp.single_eq_of_ne hj.symm
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  have h_dW : d • W = v := by
    apply b.repr.injective
    ext i
    have h_lhs : b.repr (d • W) i = d * w i := by
      simp only [map_zsmul, Finsupp.coe_smul, Pi.smul_apply,
        Int.zsmul_eq_mul, mul_eq_mul_left_iff]
      rw [LinearEquiv.apply_symm_apply]
      rw [h_W_repr_i i]
      simp only [true_or]
    rw [h_lhs]
    have h_cw := hw i
    exact h_cw.symm
  have hd_unit : IsUnit d := h_prim d W h_dW
  have h_1_in : (1 : ℤ) ∈ I := by
    rw [← hd, Submodule.mem_span_singleton]
    obtain ⟨u, hu⟩ := hd_unit
    use ↑(u⁻¹)
    rw [← hu, smul_eq_mul]
    exact Units.inv_mul u
  obtain ⟨nu_lin, h_nu_one⟩ := LinearMap.mem_range.mp h_1_in
  use nu_lin
  exact h_nu_one

section LambdaProjection
/-!
## Projection on cyclotomic coefficients

This section constructs the additive projection `nu : Lambda k G →+ ℤ` and
its auxiliary extension `nu_ext : k → k`.
-/

variable {G : Type v} [Group G] [Finite G]
variable {k : Type u} [Field k] [CharZero k]

/--
Bernstein's Lemma 2 for the coefficient ring `Λ`.

There is an additive homomorphism `ν : Λ → ℤ` sending `1` to `1`.
-/
lemma exists_projection
    [Module.Finite ℤ (ClassFun.Lambda k G)] [Module.Free ℤ (ClassFun.Lambda k G)] :
    ∃ ν : (ClassFun.Lambda k G) →+ ℤ, ν 1 = 1 := by
  have h_prim : ∀ (m : ℤ) (x : ClassFun.Lambda k G), m • x = 1 → IsUnit m :=
    ClassFun.Lambda.one_is_primitive (G := G) (k:=k)
  obtain ⟨nu_lin, h_nu_one⟩ := exists_projection_of_primitive (1 : ClassFun.Lambda k G) h_prim
  use nu_lin.toAddMonoidHom
  exact h_nu_one

/--
A chosen Bernstein projection `ν : Λ → ℤ`.
-/
@[expose] noncomputable def nu
    (k : Type u) [Field k] [CharZero k]
    (G : Type v) [Group G] [Finite G] :
    ClassFun.Lambda k G →+ ℤ := by
  haveI : NeZero (Nat.card G) :=
    ⟨One.natCard_ne_zero_of_finite G⟩
  exact Classical.choose (exists_projection (G := G) (k := k))

@[simp]
lemma nu_zero :
    nu k G 0 = 0 := by
  exact (nu k G).map_zero

lemma nu_one : nu k G 1 = 1 := by
  haveI : NeZero (Nat.card G) := ⟨One.natCard_ne_zero_of_finite G⟩
  exact Classical.choose_spec (exists_projection)

open Classical in
/--
The coefficient projection extended to all of `k` by zero outside `Λ`.

This function is only additive and `ℤ`-linear on inputs known to lie in `Λ`;
it is not intended to be a ring homomorphism on `k`.
-/
@[expose] noncomputable def nu_ext
    (k : Type u) [Field k] [CharZero k]
    (G : Type v) [Group G] [Finite G]
    (x : k) : k :=
  if h : x ∈ ClassFun.Lambda k G then (nu k G ⟨x, h⟩ : k) else 0

@[simp]
lemma nu_ext_one :
    nu_ext k G 1 = 1 := by
  have h1 : (1 : k) ∈ ClassFun.Lambda k G := Subring.one_mem _
  unfold nu_ext
  rw [dif_pos h1]
  change ((nu k G) (1 : ClassFun.Lambda k G) : k) = 1
  rw [nu_one, Int.cast_one]

@[simp]
lemma nu_ext_zero :
    nu_ext k G 0 = 0 := by
  have h0 : (0 : k) ∈ ClassFun.Lambda k G := Subring.zero_mem _
  unfold nu_ext
  rw [dif_pos h0]
  change ((nu k G) (0 : ClassFun.Lambda k G) : k) = 0
  rw [nu_zero, Int.cast_zero]

/-- nu_ext is additive on Λ -/
@[simp]
lemma nu_ext_add
    {x y : k} (hx : x ∈ ClassFun.Lambda k G) (hy : y ∈ ClassFun.Lambda k G) :
    nu_ext k G (x + y) = nu_ext k G x + nu_ext k G y := by
  have hxy : x + y ∈ ClassFun.Lambda k G := Subring.add_mem _ hx hy
  unfold nu_ext
  rw [dif_pos hx, dif_pos hy, dif_pos hxy]
  have h_add := map_add (nu k G) ⟨x, hx⟩ ⟨y, hy⟩
  change (nu k G ⟨x + y, hxy⟩ : k) = (nu k G ⟨x, hx⟩ : k) + (nu k G ⟨y, hy⟩ : k)
  rw [← Int.cast_add]
  congr 1

/-- nu_ext preserves integer scalar multiplication on Λ -/
@[simp]
lemma nu_ext_int_mul
    {x : k} (hx : x ∈ ClassFun.Lambda k G) (z : ℤ) :
    nu_ext k G ((z : k) * x) = (z : k) * nu_ext k G x := by
  have hzx : (z : k) * x ∈ ClassFun.Lambda k G := by
    have h_smul : (z : k) * x = z • x := by exact Eq.symm (zsmul_eq_mul x z)
    rw [h_smul]
    exact zsmul_mem hx z
  unfold nu_ext
  rw [dif_pos hx, dif_pos hzx]
  have h_eq : (⟨(z : k) * x, hzx⟩ : ClassFun.Lambda k G) = z • ⟨x, hx⟩ := by
    ext
    exact Eq.symm (zsmul_eq_mul x z)
  rw [h_eq, map_zsmul]
  simp only [Int.zsmul_eq_mul, Int.cast_mul]

/-- nu_ext acts as the exact identity on purely integer values. -/
@[simp]
lemma nu_ext_int
    (z : ℤ) : nu_ext k G (z : k) = (z : k) := by
  have hz : (z : k) ∈ ClassFun.Lambda k G := by
    have h_smul : (z : k) = z • (1 : k) := by
      calc (z : k) = (z : k) * 1 := (mul_one _).symm
           _ = z • (1 : k) := by exact Eq.symm (zsmul_eq_mul (1 : k) z)
    rw [h_smul]
    exact zsmul_mem (Subring.one_mem _) z
  unfold nu_ext
  rw [dif_pos hz]
  have h_eq : (⟨(z : k), hz⟩ : ClassFun.Lambda k G) = z • (1 : ClassFun.Lambda k G) := by
    ext
    calc (z : k) = (z : k) * 1 := (mul_one _).symm
         _ = z • (1 : k) := by exact Eq.symm (zsmul_eq_mul (1 : k) z)
  rw [h_eq, map_zsmul, nu_one (G:=G) (k:=k)]
  simp only [Int.zsmul_eq_mul, mul_one]

end LambdaProjection

section CharacterCoefficientProjection

/-!
## Projection on class-function coefficients

This section fixes an irreducible-character basis and applies `nu_ext` to the
coordinates of a class function. The resulting map `nuStar` fixes characters
of finite-dimensional representations. On the integral cyclotomic character
ring, it is packaged as the `ℤ`-linear map `nuStarLinear` with codomain
`ClassFun.CharacterRing k G`.
-/

variable {k : Type u} [Field k] [CharZero k]
variable {G : Type u} [Group G]

/--
Apply Bernstein's coefficient projection to the coordinates of a class function
in a fixed irreducible-character basis.
-/
@[expose] noncomputable def nuStar [Finite G]
    (B : ClassFun.IrrepCharBasis k G) (f : ClassFun k G) : ClassFun k G :=
  B.b.repr.symm
    ((B.b.repr f).mapRange
      (fun a : k => nu_ext (k := k) (G := G) a)
      (by simp))

/-- `nuStar` fixes each irreducible-character basis vector. -/
@[simp]
lemma nuStar_basis [Finite G]
    (B : ClassFun.IrrepCharBasis k G) (i : B.ι) :
    nuStar B (B.b i) = B.b i := by
  unfold nuStar
  simp

/--
The coordinates of `nuStar B f` are obtained by applying `nu_ext` to the
coordinates of `f`.
-/
@[simp]
lemma repr_nuStar_apply [Finite G]
    (B : ClassFun.IrrepCharBasis k G) (f : ClassFun k G) (i : B.ι) :
    B.b.repr (nuStar B f) i =
      nu_ext (k := k) (G := G) (B.b.repr f i) := by
  unfold nuStar
  simp

@[simp]
lemma nuStar_char_basis [Finite G]
    (B : ClassFun.IrrepCharBasis k G) (i : B.ι) :
    nuStar B (ClassFun.character (B.V i)) =
      ClassFun.character (B.V i) := by
  rw [← B.b_eq i]
  simp

@[simp]
lemma nuStar_zero [Finite G]
    (B : ClassFun.IrrepCharBasis k G) :
    nuStar B 0 = 0 := by
  apply B.b.repr.injective
  ext i
  simp

/--
`nuStar` is additive on class functions whose coordinates all lie in `Λ`.
-/
lemma nuStar_add [Finite G]
    (B : ClassFun.IrrepCharBasis k G)
    {f g : ClassFun k G}
    (hf : ClassFun.HasLambdaCoords B f)
    (hg : ClassFun.HasLambdaCoords B g) :
    nuStar B (f + g) = nuStar B f + nuStar B g := by
  apply B.b.repr.injective
  ext i
  rw [repr_nuStar_apply]
  rw [LinearEquiv.map_add]
  change
    nu_ext (k := k) (G := G) ((B.b.repr f) i + (B.b.repr g) i)
      =
    (B.b.repr (nuStar B f + nuStar B g)) i
  rw [nu_ext_add (hf i) (hg i)]
  simp

lemma nuStar_smul_char [Finite G]
    (B : ClassFun.IrrepCharBasis k G)
    {a : k} (ha : a ∈ ClassFun.Lambda k G)
    (U : FDRep k G) :
    nuStar B (a • ClassFun.character U) =
      nu_ext (k := k) (G := G) a • ClassFun.character U := by
  apply B.b.repr.injective
  ext i
  rw [repr_nuStar_apply]
  have hcoord :
      B.b.repr (a • ClassFun.character U) i =
        a * B.b.repr (ClassFun.character U) i := by
    rw [LinearEquiv.map_smul]
    rfl
  rw [hcoord]
  obtain ⟨m, hm⟩ := ClassFun.char_coeffs_int B U i
  rw [hm]
  have hmul : a * (m : k) = (m : k) * a := by ring
  rw [hmul]
  rw [nu_ext_int_mul (k := k) (G := G) ha m]
  rw [LinearEquiv.map_smul]
  simp only [Finsupp.coe_smul, Pi.smul_apply, hm, smul_eq_mul]
  ring

/--
`nuStar` commutes with integral scalar multiplication on class functions whose
coordinates all lie in `Λ`.
-/
lemma nuStar_zsmul [Finite G]
    (B : ClassFun.IrrepCharBasis k G)
    (z : ℤ) {f : ClassFun k G}
    (hf : ClassFun.HasLambdaCoords B f) :
    nuStar B (z • f) = z • nuStar B f := by
  apply B.b.repr.injective
  ext i
  rw [repr_nuStar_apply]
  have hcoord :
      B.b.repr (z • f) i = (z : k) * (B.b.repr f i) := by
    have hz :
        z • f = (z : k) • f :=
      Eq.symm (Int.cast_smul_eq_zsmul k z f)
    rw [hz, LinearEquiv.map_smul]
    rfl
  rw [hcoord]
  rw [nu_ext_int_mul (k := k) (G := G) (hf i) z]
  have hcoord_rhs :
      B.b.repr (z • nuStar B f) i =
        z • (B.b.repr (nuStar B f) i) := by
    have hz :
        z • nuStar B f = (z : k) • nuStar B f :=
      Eq.symm (Int.cast_smul_eq_zsmul k z (nuStar B f))
    rw [hz, LinearEquiv.map_smul]
    change (z : k) * (B.b.repr (nuStar B f) i) =
      z • (B.b.repr (nuStar B f) i)
    exact Eq.symm (zsmul_eq_mul (B.b.repr (nuStar B f) i) z)
  rw [hcoord_rhs, repr_nuStar_apply, zsmul_eq_mul]

/--
`nuStar` fixes the character of every finite-dimensional representation.
-/
lemma nuStar_fixes_char [Finite G]
    (B : ClassFun.IrrepCharBasis k G)
    (U : FDRep k G) :
    nuStar B (ClassFun.character U) = ClassFun.character U := by
  apply B.b.repr.injective
  ext i
  rw [repr_nuStar_apply]
  obtain ⟨m, hm⟩ := ClassFun.char_coeffs_int B U i
  rw [hm]
  simp

lemma nuStar_one [Finite G]
    (B : ClassFun.IrrepCharBasis k G) :
    nuStar B (1 : ClassFun k G) = 1 := by
  have htriv :
      ClassFun.character (FDRep.trivial k G) = (1 : ClassFun k G) :=
    ClassFun.char_trivial (k := k) (G := G)
  rw [← htriv]
  exact nuStar_fixes_char B (FDRep.trivial k G)

/--
Applying Bernstein's coefficient projection to a class function with
`Λ`-valued irreducible-character coordinates produces a virtual character.
-/
lemma nuStar_mem_characterSpan [Finite G]
    (B : ClassFun.IrrepCharBasis k G)
    {f : ClassFun k G}
    (hf : ClassFun.HasLambdaCoords B f) :
    nuStar B f ∈ ClassFun.characterSpan k G := by
  have hexpand :
      nuStar B f =
        ∑ i : B.ι, (B.b.repr (nuStar B f) i) • B.b i := by
    simp only [Module.Basis.sum_repr]
  rw [hexpand]
  apply Submodule.sum_mem
  intro i _
  rw [repr_nuStar_apply]
  let z : ℤ := nu k G ⟨B.b.repr f i, hf i⟩
  have hz :
      nu_ext (k := k) (G := G) (B.b.repr f i) = (z : k) := by
    unfold nu_ext
    rw [dif_pos (hf i)]
  rw [hz, Int.cast_smul_eq_zsmul, B.b_eq]
  exact Submodule.smul_mem _ z
    (ClassFun.characterSpan.character_mem (B.V i))

/--
Bernstein's coefficient projection from integer-valued cyclotomic characters
to virtual characters.

This map is `ℤ`-linear, but it is not asserted to preserve multiplication.
-/
@[expose] noncomputable def nuStarLinear [Finite G]
    (B : ClassFun.IrrepCharBasis k G) :
    ClassFun.IntegralCyclotomicCharacterRing (k := k) (G := G) →ₗ[ℤ]
      ClassFun.CharacterRing k G where
  toFun f :=
    ⟨nuStar B (f : ClassFun k G),
      nuStar_mem_characterSpan B
        (ClassFun.R_Lambda.top_hasLambdaCoords B
          (ClassFun.IntegralCyclotomicCharacterRing.rLambda_mem f))⟩
  map_add' f g := by
    apply Subtype.ext
    change
      nuStar B ((f : ClassFun k G) + (g : ClassFun k G)) =
        nuStar B (f : ClassFun k G) +
          nuStar B (g : ClassFun k G)
    exact nuStar_add B
      (ClassFun.R_Lambda.top_hasLambdaCoords B
        (ClassFun.IntegralCyclotomicCharacterRing.rLambda_mem f))
      (ClassFun.R_Lambda.top_hasLambdaCoords B
        (ClassFun.IntegralCyclotomicCharacterRing.rLambda_mem g))
  map_smul' z f := by
    apply Subtype.ext
    change
      nuStar B (z • (f : ClassFun k G)) =
        z • nuStar B (f : ClassFun k G)
    exact nuStar_zsmul B z
      (ClassFun.R_Lambda.top_hasLambdaCoords B
        (ClassFun.IntegralCyclotomicCharacterRing.rLambda_mem f))

@[simp]
lemma coe_nuStarLinear [Finite G]
    (B : ClassFun.IrrepCharBasis k G)
    (f : ClassFun.IntegralCyclotomicCharacterRing (k := k) (G := G)) :
    (nuStarLinear B f : ClassFun k G) = nuStar B (f : ClassFun k G) :=
  rfl

@[simp]
lemma nuStarLinear_one [Finite G]
    (B : ClassFun.IrrepCharBasis k G) :
    nuStarLinear B 1 = 1 := by
  apply Subtype.ext
  exact nuStar_one B

end CharacterCoefficientProjection

end CFSG.BrauerInduction.Cyclotomic
