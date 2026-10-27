module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5Inputs
public import CFSG.LocalAnalysis.StandardType.GGExcCompFieldInput

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus

@[expose] def LangNontoralCompField :
    Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup .E6 L p₀),
    S.IsAlgebraic →
    ∀ D : Subgroup (ModGL .E6 L), D ≤ S.D.model → IsElemAbelian 3 D → Nat.card D = 3 ^ 2 →
      (¬ ∃ g ∈ adjointGroup .E6 L, ∀ x ∈ D, g⁻¹ * x * g ∈ torusGroup .E6 L) →
      ∀ K : Subgroup (ModGL .E6 L),
        IsComponentOf K (S.Γ ⊓ Subgroup.centralizer (D : Set (ModGL .E6 L))) →
        CFSG.StandardType.GGCompFieldAt S.D.q K ∨
          (S.D.q = 2 ∧ Nat.card D = 9 ∧ Nat.card K = 6048 ∧
            Nat.card (↥K ⧸ Subgroup.center ↥K) = 6048)

end CFSG.StandardType.TableCRes

end
