module

public import CFSG.LocalAnalysis.StandardType.GGExcCompSLDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyGen
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.BigAnyDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialPoly
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.Assembly (LargeEvenLabel LargeEvenInLambda2)

@[expose] def LangFamilyCompFieldSL :
    Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ p : ℕ) (S : LangSetup τ L p₀),
    (τ = .E6 ∨ τ = .E7 ∨ τ = .E8) → p.Prime → p ≠ 2 →
    ∀ (ι : Type) (a : ι → Fin τ.rank → Lˣ),
      (∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) → (∀ u j, a u j ^ p = 1) →
      ∀ K : Subgroup (ModGL τ L),
        IsComponentOf K (S.Γ ⊓ Subgroup.centralizer (Set.range fun u => rootDiagUnit τ (a u))) →
        ∃ i : KernelComponent (Pi.monoidHom fun u => rootCharHom (a u)),
          K ≤ rootSpan τ L {γ | ∃ (k : ℕ) (δ : Fin τ.rank → ℤ),
              δ ∈ componentRoots (Pi.monoidHom fun u => rootCharHom (a u)) i ∧
                γ = (S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] δ} ∧
          CFSG.StandardType.GGCompFieldAtSL
            (S.D.q ^ componentOrbitLength S.ρ
              (componentRoots (Pi.monoidHom fun u => rootCharHom (a u)) i)) K

@[expose] def LangFamilyCompFieldF4 :
    Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ p : ℕ) (S : LangSetup .F4 L p₀),
    p.Prime → p ≠ 2 →
    ∀ (ι : Type) (a : ι → Fin Tag.F4.rank → Lˣ),
      (∀ u, rootDiagUnit .F4 (a u) ∈ S.D.torus) → (∀ u j, a u j ^ p = 1) →
      ∀ K : Subgroup (ModGL .F4 L),
        IsComponentOf K (S.Γ ⊓ Subgroup.centralizer (Set.range fun u => rootDiagUnit .F4 (a u))) →
        ∃ i : KernelComponent (Pi.monoidHom fun u => rootCharHom (a u)),
          K ≤ rootSpan .F4 L {γ | ∃ (k : ℕ) (δ : Fin Tag.F4.rank → ℤ),
              δ ∈ componentRoots (Pi.monoidHom fun u => rootCharHom (a u)) i ∧
                γ = (S.ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ))^[k] δ} ∧
          (CFSG.StandardType.GGCompFieldAt
            (S.D.q ^ componentOrbitLength S.ρ
              (componentRoots (Pi.monoidHom fun u => rootCharHom (a u)) i)) K ∨
            (S.D.q = 2 ∧
              componentOrbitLength S.ρ
                (componentRoots (Pi.monoidHom fun u => rootCharHom (a u)) i) = 1 ∧
              Nat.card K = 360 ∧
              Nat.card (↥K ⧸ Subgroup.center ↥K) = 360))

end CFSG.StandardType.TableCRes

end
