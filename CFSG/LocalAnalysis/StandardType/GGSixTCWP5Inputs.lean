module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Inputs
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Inputs2
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus

@[expose] def GGTCInputG6InnerDiagLangTw :
    Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup .E6 L p₀),
    (¬ ∃ w : WeylGroup .E6, ∀ γ, IsRoot .E6 γ → S.ρ γ = w • γ) →
    ∀ d t : Fin Tag.E6.rank → Lˣ, rootDiagUnit .E6 d ∈ S.D.torus → rootDiagUnit .E6 t ∈ S.D.torus →
      (∀ j, d j ^ 3 = 1) → (∀ j, t j ^ 3 = 1) → rootDiagUnit .E6 d ≠ 1 →
      ∀ K : Subgroup (ModGL .E6 L),
        IsComponentOf K (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit .E6 d}) →
        CFSG.StandardType.GGInnerDiagOn (Subgroup.zpowers (rootDiagUnit .E6 t)) K

@[expose] def TwE6q2OrderThreeCentralizers : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n : ℕ), LieModel G .twistedE6 n 2 1 →
    ∀ g : G, orderOf g = 3 →
      ¬ 13 ∣ Nat.card (Subgroup.centralizer ({g} : Set G)) ∧
        ¬ 19 ∣ Nat.card (Subgroup.centralizer ({g} : Set G))

end CFSG.StandardType.TableCRes

end
