module

public import CFSG.LocalAnalysis.StandardType.GGQTwoPosInLCells
public import CFSG.LocalAnalysis.StandardType.GGQTwoModel
public import CFSG.LocalAnalysis.StandardType.GGQTwoPairsDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoReflLin
public import CFSG.LocalAnalysis.StandardType.GGQTwoQuandleSym

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

@[expose] def d6SumZero : Submodule (ZMod 3) (Fin 6 → ZMod 3) :=
  LinearMap.ker (∑ i : Fin 6, (LinearMap.proj i : (Fin 6 → ZMod 3) →ₗ[ZMod 3] ZMod 3))

@[expose] def d6PermAct (σ : Equiv.Perm (Fin 6)) :
    (Fin 6 → ZMod 3) ≃ₗ[ZMod 3] (Fin 6 → ZMod 3) :=
  LinearEquiv.funCongrLeft (ZMod 3) (ZMod 3) σ.symm

theorem d6PermAct_mem (σ : Equiv.Perm (Fin 6)) {v : Fin 6 → ZMod 3} (hv : v ∈ d6SumZero) :
    d6PermAct σ v ∈ d6SumZero := by
  simp only [d6SumZero, LinearMap.mem_ker, LinearMap.sum_apply, LinearMap.proj_apply] at hv ⊢
  rw [← hv]
  exact Equiv.sum_comp σ.symm v

structure D6Mod (V : Type) [AddCommGroup V] [Module (ZMod 3) V] where
  ρ : Equiv.Perm (Fin 6) →* (V ≃ₗ[ZMod 3] V)
  μ : d6SumZero →ₗ[ZMod 3] V
  μ_inj : Function.Injective μ
  μ_comm : ∀ (σ : Equiv.Perm (Fin 6)) (v : d6SumZero),
    ρ σ (μ v) = μ ⟨d6PermAct σ v, d6PermAct_mem σ v.2⟩
  triv : ∀ (σ : Equiv.Perm (Fin 6)) (v : V), ρ σ v - v ∈ LinearMap.range μ

@[expose] def IsRefl3 {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (g : V ≃ₗ[ZMod 3] V) : Prop :=
  g * g = 1 ∧ Nat.card {v : V // g v = v} * 3 = Nat.card V

end CFSG.StandardType

end
