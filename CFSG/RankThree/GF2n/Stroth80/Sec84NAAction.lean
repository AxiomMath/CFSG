module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

section InducedAction

variable {Γ : Type} [Group Γ] {K : Type} [Field K] {E : Type} [AddCommGroup E] [Module K E]
  [DistribMulAction Γ E] [SMulCommClass Γ K E]

@[expose] def NAInvSub (V : Submodule K E) (_ : ∀ g : Γ, ∀ x ∈ V, g • x ∈ V) : Type := ↥V

instance (V : Submodule K E) (hV : ∀ g : Γ, ∀ x ∈ V, g • x ∈ V) :
    AddCommGroup (NAInvSub V hV) := inferInstanceAs (AddCommGroup ↥V)

instance (V : Submodule K E) (hV : ∀ g : Γ, ∀ x ∈ V, g • x ∈ V) :
    Module K (NAInvSub V hV) := inferInstanceAs (Module K ↥V)

instance (V : Submodule K E) (hV : ∀ g : Γ, ∀ x ∈ V, g • x ∈ V) :
    DistribMulAction Γ (NAInvSub V hV) where
  smul g x := (⟨g • (x : ↥V).1, hV g (x : ↥V).1 (x : ↥V).2⟩ : ↥V)
  one_smul x := Subtype.ext (one_smul Γ (x : ↥V).1)
  mul_smul g h x := Subtype.ext (mul_smul g h (x : ↥V).1)
  smul_zero g := Subtype.ext (smul_zero g)
  smul_add g x y := Subtype.ext (smul_add g (x : ↥V).1 (y : ↥V).1)

instance (V : Submodule K E) (hV : ∀ g : Γ, ∀ x ∈ V, g • x ∈ V) :
    SMulCommClass Γ K (NAInvSub V hV) :=
  ⟨fun g c x => Subtype.ext (smul_comm g c (x : ↥V).1)⟩

@[expose] def NAInvSub.mk (V : Submodule K E) (hV : ∀ g : Γ, ∀ x ∈ V, g • x ∈ V) (x : E)
    (hx : x ∈ V) : NAInvSub V hV := (⟨x, hx⟩ : ↥V)

theorem NAInvSub.smul_mk (V : Submodule K E) (hV : ∀ g : Γ, ∀ x ∈ V, g • x ∈ V) (g : Γ) (x : E)
    (hx : x ∈ V) :
    g • NAInvSub.mk V hV x hx = NAInvSub.mk V hV (g • x) (hV g x hx) := rfl

@[expose] def NAInvQuot (V : Submodule K E) (_ : ∀ g : Γ, ∀ x ∈ V, g • x ∈ V) : Type := E ⧸ V

instance (V : Submodule K E) (hV : ∀ g : Γ, ∀ x ∈ V, g • x ∈ V) :
    AddCommGroup (NAInvQuot V hV) := inferInstanceAs (AddCommGroup (E ⧸ V))

instance (V : Submodule K E) (hV : ∀ g : Γ, ∀ x ∈ V, g • x ∈ V) :
    Module K (NAInvQuot V hV) := inferInstanceAs (Module K (E ⧸ V))

@[expose] def NAInvQuot.mk (V : Submodule K E) (hV : ∀ g : Γ, ∀ x ∈ V, g • x ∈ V) (x : E) :
    NAInvQuot V hV := Submodule.Quotient.mk (p := V) x

@[expose] def quotActLin (V : Submodule K E) (hV : ∀ g : Γ, ∀ x ∈ V, g • x ∈ V) (g : Γ) :
    (E ⧸ V) →ₗ[K] (E ⧸ V) :=
  Submodule.mapQ V V (DistribMulAction.toLinearEquiv K E g : E ≃ₗ[K] E).toLinearMap
    (fun x hx => hV g x hx)

instance (V : Submodule K E) (hV : ∀ g : Γ, ∀ x ∈ V, g • x ∈ V) :
    DistribMulAction Γ (NAInvQuot V hV) where
  smul g q := quotActLin V hV g q
  one_smul q := by
    induction q using Submodule.Quotient.induction_on with
    | H x => exact congrArg Submodule.Quotient.mk (one_smul Γ x)
  mul_smul g h q := by
    induction q using Submodule.Quotient.induction_on with
    | H x => exact congrArg Submodule.Quotient.mk (mul_smul g h x)
  smul_zero g := map_zero (quotActLin V hV g)
  smul_add g a b := map_add (quotActLin V hV g) a b

theorem NAInvQuot.smul_mk (V : Submodule K E) (hV : ∀ g : Γ, ∀ x ∈ V, g • x ∈ V) (g : Γ) (x : E) :
    g • NAInvQuot.mk V hV x = NAInvQuot.mk V hV (g • x) := rfl

instance (V : Submodule K E) (hV : ∀ g : Γ, ∀ x ∈ V, g • x ∈ V) :
    SMulCommClass Γ K (NAInvQuot V hV) :=
  ⟨fun g c q => map_smul (quotActLin V hV g) c q⟩

theorem NAInvQuot.mk_add (V : Submodule K E) (hV : ∀ g : Γ, ∀ x ∈ V, g • x ∈ V) (x y : E) :
    NAInvQuot.mk V hV (x + y) = NAInvQuot.mk V hV x + NAInvQuot.mk V hV y := rfl

theorem NAInvQuot.mk_eq_zero (V : Submodule K E) (hV : ∀ g : Γ, ∀ x ∈ V, g • x ∈ V) (x : E) :
    NAInvQuot.mk V hV x = 0 ↔ x ∈ V := Submodule.Quotient.mk_eq_zero V

theorem NAInvQuot.mk_eq_mk (V : Submodule K E) (hV : ∀ g : Γ, ∀ x ∈ V, g • x ∈ V) (x y : E) :
    NAInvQuot.mk V hV x = NAInvQuot.mk V hV y ↔ x - y ∈ V := Submodule.Quotient.eq V

theorem NAInvQuot.mk_surjective (V : Submodule K E) (hV : ∀ g : Γ, ∀ x ∈ V, g • x ∈ V) :
    Function.Surjective (NAInvQuot.mk V hV) := Submodule.Quotient.mk_surjective V

instance (V : Submodule K E) (hV : ∀ g : Γ, ∀ x ∈ V, g • x ∈ V) [Module.Finite K E] :
    Module.Finite K (NAInvSub V hV) := inferInstanceAs (Module.Finite K ↥V)

instance (V : Submodule K E) (hV : ∀ g : Γ, ∀ x ∈ V, g • x ∈ V) [Module.Finite K E] :
    Module.Finite K (NAInvQuot V hV) := inferInstanceAs (Module.Finite K (E ⧸ V))

end InducedAction

end CFSG.RankThree.GF2n.Stroth80
