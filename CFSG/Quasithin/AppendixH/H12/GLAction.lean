module

public import CFSG.Quasithin.Background.H12OneHatM22PfSyl

public section

namespace CFSG.Quasithin.AppendixH.H12.Model

open CFSG.Quasithin.H.Mathieu.H12Pf (glMul toAdd_glMul)

abbrev Γ12 : Type := GL (Fin 12) (ZMod 2)

abbrev Vec12 : Type := Multiplicative (Fin 12 → ZMod 2)

@[expose] def glHom : Γ12 →* MulAut Vec12 where
  toFun := glMul
  map_one' := by
    refine MulEquiv.ext fun v => ?_
    show glMul 1 v = v
    apply Multiplicative.toAdd.injective
    rw [toAdd_glMul]; simp
  map_mul' g h := by
    refine MulEquiv.ext fun v => ?_
    show glMul (g * h) v = glMul g (glMul h v)
    apply Multiplicative.toAdd.injective
    rw [toAdd_glMul, toAdd_glMul, toAdd_glMul, Units.val_mul, Matrix.mulVec_mulVec]

theorem toAdd_glHom (g : Γ12) (v : Vec12) :
    Multiplicative.toAdd (glHom g v) =
      (g : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec (Multiplicative.toAdd v) := rfl

theorem glHom_injective : Function.Injective glHom := by
  intro g h hgh
  apply Units.ext
  ext i j
  have h1 := congrFun (congrArg (fun φ : MulAut Vec12 =>
    Multiplicative.toAdd (φ (Multiplicative.ofAdd (Pi.single j 1)))) hgh) i
  simpa [toAdd_glHom, Matrix.mulVec_single] using h1

end CFSG.Quasithin.AppendixH.H12.Model
