module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3LatticeDefs

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag)
open CFSG.LieType.Steinberg.Adjoint (iform)
open Matrix

@[expose] def A3SpecE6Struct : Prop :=
  ∀ c₁ c₂ : Fin (langTag .E6).rank → ZMod 3,
    (∀ s t : ZMod 3, s • c₁ + t • c₂ = 0 → s = 0 ∧ t = 0) →
    ∀ m ∈ a3Ker (langTag .E6) c₁ c₂, (a3Comp (langTag .E6) c₁ c₂ m).ncard = 12 →
      ∃ β₀ β₁ : Fin (langTag .E6).rank → ℤ,
        IsRoot (langTag .E6) β₀ ∧ IsRoot (langTag .E6) β₁ ∧ iform β₀ β₁ = 0 ∧
        (∀ γ, IsRoot (langTag .E6) γ →
          ((∀ ψ ∈ a3Comp (langTag .E6) c₁ c₂ m, iform ψ γ = 0) ↔
            (γ = β₀ ∨ γ = -β₀ ∨ γ = β₁ ∨ γ = -β₁))) ∧
        (∀ γ, IsRoot (langTag .E6) γ →
          ((iform γ β₀ = 0 ∧ iform γ β₁ = 0) ↔ γ ∈ a3Comp (langTag .E6) c₁ c₂ m)) ∧
        (∃ ψ₀ ∈ a3Comp (langTag .E6) c₁ c₂ m, ∃ ψ₁ ∈ a3Comp (langTag .E6) c₁ c₂ m,
          iform ψ₀ ψ₁ = 0) ∧
        (∀ ψ ∈ a3Comp (langTag .E6) c₁ c₂ m, ∃ x ∈ a3Comp (langTag .E6) c₁ c₂ m,
          ∃ y ∈ a3Comp (langTag .E6) c₁ c₂ m, ψ = x + y) ∧
        (∀ x : WeylGroup (langTag .E6), (∀ γ ∈ a3Comp (langTag .E6) c₁ c₂ m, x • γ = γ) →
          x = 1 ∨ x = rootReflection β₀ ∨ x = rootReflection β₁ ∨
            x = rootReflection β₀ * rootReflection β₁)

@[expose] noncomputable def ggLieCorootUnit (β : Fin (langTag .E6).rank → ℤ) :
    Fin (langTag .E6).rank → GGLˣ :=
  fun j => ggZeta 3 Nat.prime_three (by norm_num) ^ iform (Pi.single j 1) β

@[expose] def GGLieA3LatticeE6 : Prop :=
  ∀ (w w' : WeylGroup (langTag .E6)) (a₁ a₂ : Fin (langTag .E6).rank → GGLˣ),
    (∀ i, a₁ i ^ 3 = 1) → (∀ i, a₂ i ^ 3 = 1) →
    (∀ γ, IsRoot (langTag .E6) γ → rootChar a₁ (w • γ) = rootChar a₁ γ ^ 2) →
    (∀ γ, IsRoot (langTag .E6) γ → rootChar a₂ (w • γ) = rootChar a₂ γ ^ 2) →
    Nat.card (Subgroup.closure
      {rootDiagUnit (langTag .E6) a₁, rootDiagUnit (langTag .E6) a₂}) = 3 ^ 2 →
    ∀ i : KernelComponent (jointChar a₁ a₂),
      (componentRoots (jointChar a₁ a₂) i).ncard = 12 →
      w' ∈ Subgroup.closure {s : WeylGroup (langTag .E6) |
        ∃ γ ∈ componentRoots (jointChar a₁ a₂) i, s = rootReflection γ} →
      (∀ γ ∈ componentRoots (jointChar a₁ a₂) i, w • γ = w' • γ) →
      ∃ β₀ β₁ : Fin (langTag .E6).rank → ℤ,
        IsRoot (langTag .E6) β₀ ∧ IsRoot (langTag .E6) β₁ ∧ iform β₀ β₁ = 0 ∧
        kernelRoots (jointChar a₁ a₂) = componentRoots (jointChar a₁ a₂) i ∧
        componentRoots (jointChar a₁ a₂) i =
          {γ | IsRoot (langTag .E6) γ ∧ iform γ β₀ = 0 ∧ iform γ β₁ = 0} ∧
        w = w' * rootReflection β₀ * rootReflection β₁ ∧
        (∃ ψ₀ ∈ componentRoots (jointChar a₁ a₂) i, ∃ ψ₁ ∈ componentRoots (jointChar a₁ a₂) i,
          iform ψ₀ ψ₁ = 0) ∧
        (∀ ψ ∈ componentRoots (jointChar a₁ a₂) i, ∃ x ∈ componentRoots (jointChar a₁ a₂) i,
          ∃ y ∈ componentRoots (jointChar a₁ a₂) i, ψ = x + y) ∧
        Subgroup.closure {rootDiagUnit (langTag .E6) a₁, rootDiagUnit (langTag .E6) a₂} =
          Subgroup.closure {rootDiagUnit (langTag .E6) (ggLieCorootUnit β₀),
            rootDiagUnit (langTag .E6) (ggLieCorootUnit β₁)}

end CFSG.StandardType.LieCore
