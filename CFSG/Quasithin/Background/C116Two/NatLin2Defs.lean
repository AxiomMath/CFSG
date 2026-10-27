module

public import CFSG.Quasithin.Background.C116Two.NatMod

public section

namespace CFSG.Quasithin.C116Two

open CFSG.QuasithinUnique CFSG.Open

@[expose] def addMap {N : Type} [AddCommGroup N] (g : MulAut (Multiplicative N)) (x : N) : N :=
  Multiplicative.toAdd (g (Multiplicative.ofAdd x))

@[expose] def IsSemilinear {F N : Type} [Field F] [AddCommGroup N] [Module F N] (σ : F ≃+* F)
    (g : MulAut (Multiplicative N)) : Prop :=
  ∀ (c : F) (x : N), addMap g (c • x) = σ c • addMap g x

theorem addMap_mul {N : Type} [AddCommGroup N] (g h : MulAut (Multiplicative N)) (x : N) :
    addMap (g * h) x = addMap g (addMap h x) := rfl

theorem addMap_add {N : Type} [AddCommGroup N] (g : MulAut (Multiplicative N)) (x y : N) :
    addMap g (x + y) = addMap g x + addMap g y := by
  simp [addMap, ofAdd_add]

theorem addMap_one {N : Type} [AddCommGroup N] (x : N) :
    addMap (1 : MulAut (Multiplicative N)) x = x := rfl

end CFSG.Quasithin.C116Two
