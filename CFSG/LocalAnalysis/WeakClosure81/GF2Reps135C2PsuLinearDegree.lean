module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection2.EndFieldRep
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients.Basic
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Module

theorem w135c2_psu_linear_degree {G V : Type} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] (ρ : Representation (ZMod 2) G V) (hirr : ρ.IsIrreducible) {s : ℕ}
    (hE : Nat.card (Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule) = 2 ^ s)
    (τ : V →ₗ[ZMod 2] V)
    (hτ : ∀ (T : Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule) (v : V), τ (T v) = T (τ v)) :
    s ∣ finrank (ZMod 2) (LinearMap.range (τ - 1)) := by
  classical
  let E := Module.End (MonoidAlgebra (ZMod 2) G) ρ.asModule
  haveI hirr' : ρ.IsIrreducible := hirr
  haveI : Field E := endField_field ρ
  let τE : ρ.asModule →ₗ[E] ρ.asModule :=
    { toFun := τ
      map_add' := fun x y => map_add τ x y
      map_smul' := fun T v => hτ T v }
  let R : Submodule E ρ.asModule := LinearMap.range (τE - 1)
  have hR : R.restrictScalars (ZMod 2) =
      LinearMap.range ((τ : ρ.asModule →ₗ[ZMod 2] ρ.asModule) - 1) :=
    Submodule.ext fun _ => Iff.rfl
  have hcardE : Nat.card E = 2 ^ finrank (ZMod 2) E := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E), Nat.card_zmod]
  have hfinE : finrank (ZMod 2) E = s := by
    apply Nat.pow_right_injective (by norm_num : 2 ≤ 2)
    change 2 ^ finrank (ZMod 2) E = 2 ^ s
    rw [← hcardE, hE]
  have htower : finrank (ZMod 2) E * finrank E (R.restrictScalars (ZMod 2)) =
      finrank (ZMod 2) (R.restrictScalars (ZMod 2)) :=
    Module.finrank_mul_finrank (F := ZMod 2) (K := E) (A := R.restrictScalars (ZMod 2))
  have hdvd : s ∣ finrank (ZMod 2) (R.restrictScalars (ZMod 2)) := by
    refine ⟨finrank E (R.restrictScalars (ZMod 2)), ?_⟩
    rw [← htower, hfinE]
  rw [hR] at hdvd
  exact hdvd

end CFSG.LocalAnalysis.WeakClosure81
