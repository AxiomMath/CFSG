module

public import CFSG.LocalAnalysis.StandardType.GGTPWeightAbs
public import CFSG.LocalAnalysis.StandardType.GGTPTorusLift
public import CFSG.LocalAnalysis.StandardType.GGTPTorusPSL6
public import CFSG.LocalAnalysis.StandardType.GGTPTorusPSU6

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTPWeight_PSL6 {K : Type} [Field K] [Finite K] [CharP K 2] (h3 : 3 ∣ Nat.card K - 1)
    {X : Type} [Group X] [Finite X]
    (π : X →* LargeEvenProj (LargeEvenSLGroup (Fin 6) K)) (hπ : Function.Surjective π)
    (hker : ¬ 3 ∣ Nat.card π.ker) {F : Type} [Field F] [CharP F 2] {V : Type} [AddCommGroup V]
    [Module F V] [Module.Finite F V] (ρ : X →* LinearMap.GeneralLinearGroup F V)
    (hρ : Function.Injective ρ) : 20 ≤ Module.finrank F V := by
  obtain ⟨δ, w, hδ, hw⟩ := ggTPTorus_PSL6 h3
  obtain ⟨θ, -, hθ, hperm⟩ := ggTPTorusLift π hπ hker δ hδ w hw
  exact ggTPWeight_abstract ρ hρ θ hθ hperm

theorem ggTPWeight_PSU6 {K : Type} [Field K] [Finite K] [CharP K 2] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (h3 : 3 ∣ q + 1) {X : Type} [Group X] [Finite X]
    (π : X →* LargeEvenProj (LargeEvenSUGroup (Fin 6) K q)) (hπ : Function.Surjective π)
    (hker : ¬ 3 ∣ Nat.card π.ker) {F : Type} [Field F] [CharP F 2] {V : Type} [AddCommGroup V]
    [Module F V] [Module.Finite F V] (ρ : X →* LinearMap.GeneralLinearGroup F V)
    (hρ : Function.Injective ρ) : 20 ≤ Module.finrank F V := by
  obtain ⟨δ, w, hδ, hw⟩ := ggTPTorus_PSU6 hK h3
  obtain ⟨θ, -, hθ, hperm⟩ := ggTPTorusLift π hπ hker δ hδ w hw
  exact ggTPWeight_abstract ρ hρ θ hθ hperm

end CFSG.StandardType

end
