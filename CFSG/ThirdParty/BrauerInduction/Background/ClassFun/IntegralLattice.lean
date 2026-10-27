module

public import CFSG.ThirdParty.BrauerInduction.Background.ClassFun.Integral
public import CFSG.ThirdParty.BrauerInduction.Background.ClassFun.ConjClasses
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.StdBasis

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# The lattice of integer-valued class functions

This file packages the integer-valued class functions as a subring of all
class functions.

When the coefficient ring has characteristic zero, pointwise integer casting
identifies this ring with `ClassFun ℤ G`. For finite `G`, this gives it the
structure of a finite free `ℤ`-module, with one basis element for each
conjugacy class.
-/

universe u v

namespace CFSG.ClassFun

variable {k : Type u} [CommRing k]
variable {G : Type v} [Group G]

/--
The ring of integer-valued `k`-valued class functions.

This is the full lattice `C_Z(G)`, without the cyclotomic-coordinate condition
imposed by `IntegralCyclotomicCharacterRing`.
-/
@[expose] def IntegerValued :
    Subring (ClassFun k G) where
  carrier := C_Z k G
  zero_mem' := C_Z.zero_mem
  one_mem' := C_Z.one_mem
  add_mem' := C_Z.add_mem
  mul_mem' := C_Z.mul_mem
  neg_mem' := C_Z.neg_mem

namespace IntegerValuedClassFun

@[simp]
lemma mem_iff
    {f : ClassFun k G} :
    f ∈ IntegerValued ↔ f ∈ C_Z k G :=
  Iff.rfl

/--
Pointwise integer casting, with codomain restricted to the integer-valued
class functions.
-/
@[expose] def mapIntCastRingHom :
    ClassFun ℤ G →+*
      IntegerValued (k := k) (G := G) where
  toFun ψ :=
    ⟨mapIntCast ψ, fun g => ⟨ψ g, rfl⟩⟩
  map_zero' := by
    apply Subtype.ext
    ext g
    simp
  map_one' := by
    apply Subtype.ext
    ext g
    simp
  map_add' ψ χ := by
    apply Subtype.ext
    ext g
    simp
  map_mul' ψ χ := by
    apply Subtype.ext
    ext g
    simp

@[simp]
lemma coe_mapIntCastRingHom
    (ψ : ClassFun ℤ G) :
    (mapIntCastRingHom (k := k) (G := G) ψ : ClassFun k G) =
        mapIntCast ψ :=
  rfl

/--
The unique integer representing the value of an integer-valued class function.
-/
@[expose] noncomputable def intValue
    (f : IntegerValued (k := k) (G := G))
    (g : G) :
    ℤ := Classical.choose (f.property g)

lemma intValue_spec
    (f : IntegerValued (k := k) (G := G))
    (g : G) :
    (f : ClassFun k G) g = (intValue f g : k) :=
  Classical.choose_spec (f.property g)

section CharZero

variable [CharZero k]
/--
The `ℤ`-valued class function underlying an integer-valued `k`-valued class
function.
-/
@[expose] noncomputable def intLift
    (f : IntegerValued (k := k) (G := G)) :
    ClassFun ℤ G where
  toFun := intValue f
  map_conj := by
    intro x y hxy
    apply
      (Int.cast_injective :
        Function.Injective (fun z : ℤ => (z : k)))
    calc
      (intValue f x : k)
          = (f : ClassFun k G) x :=
            (intValue_spec f x).symm
      _ = (f : ClassFun k G) y :=
            ClassFun.apply_eq_apply_of_isConj hxy
      _ = (intValue f y : k) :=
            intValue_spec f y

@[simp]
lemma mapIntCast_intLift
    (f : IntegerValued (k := k) (G := G)) :
    mapIntCastRingHom (k := k) (G := G) (intLift f) = f := by
  apply Subtype.ext
  ext g
  exact (intValue_spec f g).symm

lemma mapIntCastRingHom_injective :
    Function.Injective
      (mapIntCastRingHom (k := k) (G := G)) := by
  intro ψ χ h
  ext g
  have hg :=
    congrArg
      (fun f :
        IntegerValued (k := k) (G := G) =>
          (f : ClassFun k G) g)
      h
  exact Int.cast_injective hg

@[simp]
lemma intLift_mapIntCast
    (ψ : ClassFun ℤ G) :
    intLift
        (mapIntCastRingHom (k := k) (G := G) ψ) =
      ψ := by
  apply mapIntCastRingHom_injective (k := k) (G := G)
  rw [mapIntCast_intLift]

/--
Integer-valued `k`-valued class functions are canonically equivalent to
`ℤ`-valued class functions.
-/
noncomputable def mapIntCastRingEquiv :
    ClassFun ℤ G ≃+*
      IntegerValued (k := k) (G := G) where
  toFun := mapIntCastRingHom
  invFun := intLift
  left_inv := intLift_mapIntCast
  right_inv := mapIntCast_intLift
  map_mul' ψ χ := mapIntCastRingHom.map_mul ψ χ
  map_add' ψ χ := mapIntCastRingHom.map_add ψ χ

/--
The corresponding `ℤ`-linear equivalence.
-/
noncomputable def mapIntCastLinearEquiv :
    ClassFun ℤ G ≃ₗ[ℤ]
      IntegerValued (k := k) (G := G) :=
  mapIntCastRingEquiv.toAddEquiv.toIntLinearEquiv

/--
If every value of an integer-valued class function is divisible by a nonzero
integer `n`, then the class function itself is an `n`-fold multiple in the
integer-valued class-function lattice.
-/
lemma exists_zsmul_eq_of_intLift_dvd
    (n : ℤ) (hn : n ≠ 0)
    (f : IntegerValued (k := k) (G := G))
    (hf : ∀ g : G, n ∣ intLift f g) :
    ∃ q : IntegerValued (k := k) (G := G),
      n • q = f := by
  let ψ : ClassFun ℤ G :=
    { toFun := fun g => Classical.choose (hf g)
      map_conj := by
        intro x y hxy
        apply mul_left_cancel₀ hn
        calc
          n * Classical.choose (hf x)
              = intLift f x :=
                (Classical.choose_spec (hf x)).symm
          _ = intLift f y :=
                ClassFun.apply_eq_apply_of_isConj hxy
          _ = n * Classical.choose (hf y) :=
                Classical.choose_spec (hf y) }

  refine
    ⟨mapIntCastRingHom (k := k) (G := G) ψ, ?_⟩
  rw [← mapIntCast_intLift f, ← map_zsmul]
  apply congrArg (mapIntCastRingHom (k := k) (G := G))
  ext g
  change n * ψ g = intLift f g
  exact (Classical.choose_spec (hf g)).symm

/--
The basis of integer-valued class functions indexed by conjugacy classes.
-/
noncomputable def basis [Finite G] :
    Module.Basis (ConjClasses G) ℤ
      (IntegerValued (k := k) (G := G)) := by
  letI : Fintype G := Fintype.ofFinite G
  exact
    (Pi.basisFun ℤ (ConjClasses G)).map
      (linearEquivConjClasses.symm.trans mapIntCastLinearEquiv)

noncomputable instance instFree [Finite G] :
    Module.Free ℤ
      (IntegerValued (k := k) (G := G)) :=
  Module.Free.of_basis basis

noncomputable instance instFinite [Finite G] :
    Module.Finite ℤ
      (IntegerValued (k := k) (G := G)) := by
  letI : Fintype G := Fintype.ofFinite G
  exact Module.Finite.of_basis basis


end CharZero

end IntegerValuedClassFun
end CFSG.ClassFun
