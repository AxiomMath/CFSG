module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoTorus
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoModuleTorus
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoModuleOrbit
public import Mathlib.Algebra.Module.Submodule.EqLocus
public import Mathlib.LinearAlgebra.Dimension.Finrank

public section

namespace CFSG.StandardType.USixTwo

open CFSG.Assembly

variable {K : Type} [Field K]

theorem twenty_le_finrank_of_injective (hK : Nat.card K = 4) {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V]
    (ρ : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →* (V ≃ₗ[ZMod 2] V))
    (hρ : Function.Injective ρ) : 20 ≤ Module.finrank (ZMod 2) V := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  obtain ⟨ω, hω⟩ := exists_root_omega hK
  exact MainProof.twenty_le_finrank_of_faithful ρ hK hω hρ

theorem finrank_eq_twenty_of_finrank_fixed_threeA (hK : Nat.card K = 4) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →* (V ≃ₗ[ZMod 2] V))
    (htor : ∀ v : V, (∀ x ∈ torU K, ρ x v = v) → v = 0)
    (h8 : Module.finrank (ZMod 2)
      (LinearMap.eqLocus (ρ (threeA hω) : V →ₗ[ZMod 2] V) LinearMap.id) = 8) :
    Module.finrank (ZMod 2) V = 20 := by
  haveI : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  exact MainProof.finrank_eq_twenty_of_fixed ρ hK hω htor h8

end CFSG.StandardType.USixTwo

end
