module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreDefs

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def GGLieCentIIPlane3
    (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (D : LangDatum τ L)
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)), FrobRootMap D ρ → Finite D.model →
    (∃ f : ℕ, 1 ≤ f ∧ D.q = 2 ^ f) → ∀ (a₁ a₂ : Fin τ.rank → Lˣ),
      rootDiagUnit τ a₁ ∈ D.torus → rootDiagUnit τ a₂ ∈ D.torus →
      rootDiagUnit τ a₁ ^ 3 = 1 → rootDiagUnit τ a₂ ^ 3 = 1 →
      Nat.card ↥(Subgroup.closure {rootDiagUnit τ a₁, rootDiagUnit τ a₂}) = 3 ^ 2 →
      ∀ J : Subgroup (ModGL τ L),
        IsComponentOf J (D.Γ ⊓ Subgroup.centralizer
          ((Subgroup.closure {rootDiagUnit τ a₁, rootDiagUnit τ a₂} : Subgroup (ModGL τ L)) :
            Set (ModGL τ L))) →
        ∃ i : KernelComponent (jointChar a₁ a₂),
          J = ratComp ρ D.Γ (componentRoots (jointChar a₁ a₂) i)

@[expose] def GGLieSmallFormA8Plane3
    (τ : Tag) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (D : LangDatum τ L)
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)), FrobRootMap D ρ → Finite D.model →
    (∃ f : ℕ, 1 ≤ f ∧ D.q = 2 ^ f) → ∀ (a₁ a₂ : Fin τ.rank → Lˣ),
      rootDiagUnit τ a₁ ∈ D.torus → rootDiagUnit τ a₂ ∈ D.torus →
      rootDiagUnit τ a₁ ^ 3 = 1 → rootDiagUnit τ a₂ ^ 3 = 1 →
      Nat.card ↥(Subgroup.closure {rootDiagUnit τ a₁, rootDiagUnit τ a₂}) = 3 ^ 2 →
      ∀ (i : KernelComponent (jointChar a₁ a₂)),
        IsQuasisimple ↥(ratComp ρ D.Γ (componentRoots (jointChar a₁ a₂) i)) →
        GGSixLSevenA3Case (ratComp ρ D.Γ (componentRoots (jointChar a₁ a₂) i)) →
          compRank (componentRoots (jointChar a₁ a₂) i) = 3 ∧
          (componentRoots (jointChar a₁ a₂) i).ncard = 12 ∧
          (fun u => ρ u) '' componentRoots (jointChar a₁ a₂) i =
            componentRoots (jointChar a₁ a₂) i ∧
          twistInner (componentRoots (jointChar a₁ a₂) i) (fun u => ρ u) ∧ D.q = 2

end CFSG.StandardType.LieCore
