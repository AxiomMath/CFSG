module

public import CFSG.ThirdParty.BrauerInduction.Cyclotomic.CharacterAlgebra
public import CFSG.ThirdParty.BrauerInduction.Background.ClassFun.IntegralLattice

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# The integral cyclotomic character ring

This file packages the global character system

`Q(G) = R_Λ(G) ∩ C_Z(G)`

as a subring of the cyclotomic character algebra.
-/

universe u

namespace CFSG.ClassFun

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]

/--
The ring of integer-valued elements of the cyclotomic character algebra.

Its elements are the functions in `R_Lambda.top k G` whose values lie in the
image of `ℤ → k`. This is the global Bernstein character ring `Q(G)`.
-/
@[expose] def IntegralCyclotomicCharacterRing :
    Subring (CyclotomicCharacterAlgebra (k := k) (G := G)) where
  carrier :=
    {f |
      (f : ClassFun k G) ∈ C_Z k G}
  zero_mem' := by
    change (0 : ClassFun k G) ∈ C_Z k G
    exact C_Z.zero_mem
  one_mem' := by
    change (1 : ClassFun k G) ∈ C_Z k G
    exact C_Z.one_mem
  add_mem' := by
    intro f g hf hg
    change
      (f : ClassFun k G) + (g : ClassFun k G) ∈ C_Z k G
    exact C_Z.add_mem hf hg
  mul_mem' := by
    intro f g hf hg
    change
      (f : ClassFun k G) * (g : ClassFun k G) ∈ C_Z k G
    exact C_Z.mul_mem hf hg
  neg_mem' := by
    intro f hf
    change -(f : ClassFun k G) ∈ C_Z k G
    exact C_Z.neg_mem hf

namespace IntegralCyclotomicCharacterRing

@[simp]
lemma mem_iff
    {f : CyclotomicCharacterAlgebra (k := k) (G := G)} :
    f ∈ IntegralCyclotomicCharacterRing (k := k) (G := G) ↔
      (f : ClassFun k G) ∈ C_Z k G :=
  Iff.rfl

/-- The underlying class function belongs to the global `R_Λ` span. -/
lemma rLambda_mem
    (f : IntegralCyclotomicCharacterRing (k := k) (G := G)) :
    (f : ClassFun k G) ∈ R_Lambda.top k G :=
  f.1.property

/-- The underlying class function is integer-valued. -/
lemma intValued_mem
    (f : IntegralCyclotomicCharacterRing (k := k) (G := G)) :
    (f : ClassFun k G) ∈ C_Z k G :=
  f.property

/--
Restricting a global integral cyclotomic character to a subgroup produces an
element of the subgroup-indexed character system `Q`.
-/
lemma res_mem_Q_sys
    (H : Subgroup G)
    (f : IntegralCyclotomicCharacterRing (k := k) (G := G)) :
    ClassFun.res H (f : ClassFun k G) ∈
      ClassFun.Q_sys k G H := by
  constructor
  · exact R_Lambda.top_res_to_subgroup H f.1.property
  · exact C_Z.res f.property

/--
Restriction to the top subgroup produces an element of `Q_sys(G)`.
-/
lemma res_top_mem_Q_sys
    (f : IntegralCyclotomicCharacterRing (k := k) (G := G)) :
    ClassFun.res (⊤ : Subgroup G) (f : ClassFun k G) ∈
      ClassFun.Q_sys k G (⊤ : Subgroup G) :=
  res_mem_Q_sys ⊤ f

/--
Induction of an element of `Q(H)` regarded as an element of the global
integral cyclotomic character ring.
-/
@[expose] noncomputable def ind
    (H : Subgroup G)
    {q : ClassFun k H}
    (hq : q ∈ ClassFun.Q_sys k G H) :
    IntegralCyclotomicCharacterRing (k := k) (G := G) :=
  ⟨
    ⟨ClassFun.ind H q, R_Lambda.ind_mem_top H hq.1⟩,
    C_Z.ind_mem hq.2
  ⟩

@[simp]
lemma coe_ind
    (H : Subgroup G)
    {q : ClassFun k H}
    (hq : q ∈ ClassFun.Q_sys k G H) :
    (ind H hq : ClassFun k G) = ClassFun.ind H q :=
  rfl

/--
The inclusion of integral cyclotomic characters into all integer-valued class
functions.
-/
@[expose] def toIntegerValuedClassFun :
    IntegralCyclotomicCharacterRing (k := k) (G := G) →+*
      IntegerValued (k := k) (G := G) where
  toFun f := ⟨(f : ClassFun k G), f.property⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[simp]
lemma coe_toIntegerValuedClassFun
    (f : IntegralCyclotomicCharacterRing (k := k) (G := G)) :
    (toIntegerValuedClassFun f : ClassFun k G) =
      (f : ClassFun k G) :=
  rfl

lemma toIntegerValuedClassFun_injective :
    Function.Injective
      (toIntegerValuedClassFun (k := k) (G := G)) := by
  intro f g h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg
    (fun q :
      IntegerValued (k := k) (G := G) =>
        (q : ClassFun k G))  h

/--
The inclusion of integral cyclotomic characters into the integer-valued
class-function lattice, as a `ℤ`-linear map.
-/
@[expose] def toIntegerValuedClassFunLinear :
    IntegralCyclotomicCharacterRing (k := k) (G := G) →ₗ[ℤ]
      IntegerValued (k := k) (G := G) where
  toFun := toIntegerValuedClassFun
  map_add' _ _ := rfl
  map_smul' n f := by
    apply Subtype.ext
    rfl

@[simp]
lemma toIntegerValuedClassFunLinear_apply
    (f : IntegralCyclotomicCharacterRing (k := k) (G := G)) :
    toIntegerValuedClassFunLinear f =
      toIntegerValuedClassFun f :=
  rfl

end IntegralCyclotomicCharacterRing

end CFSG.ClassFun
