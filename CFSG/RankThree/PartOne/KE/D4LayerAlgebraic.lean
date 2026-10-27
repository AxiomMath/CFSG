module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.RankThree.PartOne.KE

theorem isAlgebraic_zmod_of_isAlgClosure {ℓ : ℕ} [Fact ℓ.Prime] {k L : Type} [Field k] [Finite k]
    [Field L] [Algebra k L] [IsAlgClosure k L] [CharP L ℓ] :
    letI := ZMod.algebra L ℓ
    Algebra.IsAlgebraic (ZMod ℓ) L := by
  have : CharP k ℓ := (Algebra.charP_iff k L ℓ).mpr inferInstance
  let _ := ZMod.algebra k ℓ
  let _ := ZMod.algebra L ℓ
  have : IsScalarTower (ZMod ℓ) k L := IsScalarTower.of_algebraMap_eq fun c =>
    congrArg (fun g : ZMod ℓ →+* L => g c) (RingHom.ext_zmod (algebraMap (ZMod ℓ) L)
      ((algebraMap k L).comp (algebraMap (ZMod ℓ) k)))
  have : Module.Finite (ZMod ℓ) k := Module.Finite.of_finite
  have : Algebra.IsAlgebraic (ZMod ℓ) k := Algebra.IsAlgebraic.of_finite (ZMod ℓ) k
  have : Algebra.IsAlgebraic k L := IsAlgClosure.isAlgebraic
  exact Algebra.IsAlgebraic.trans (ZMod ℓ) k L

end CFSG.RankThree.PartOne.KE
