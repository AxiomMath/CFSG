module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.Walter.J1Props.Multiplier
import CFSG.Walter.Models
import CFSG.GH74.Generic.GKFCover

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

@[expose] def K_SporadicCoverThreeRank : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (s : TauCeti.SporadicName),
    CFSG.Open.IsQuasisimple X →
    Odd (Nat.card (Subgroup.center X)) →
    IsSpor (X ⧸ Subgroup.center X) s →
    CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2 →
      CFSG.Open.pRank 3 (⊤ : Subgroup (X ⧸ Subgroup.center X)) ≤
        CFSG.Open.pRank 3 (⊤ : Subgroup X)

@[expose] def K_SporadicThreeRankPos : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [Nontrivial X] (s : TauCeti.SporadicName), IsSpor X s →
    1 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)

@[expose] def K_SporadicCoverCenterOdd : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (s : TauCeti.SporadicName),
    CFSG.Open.IsQuasisimple X → Odd (Nat.card (Subgroup.center X)) →
    IsSpor (X ⧸ Subgroup.center X) s →
    (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨
      s = .J2 ∨ s = .HS ∨ s = .He ∨ s = .Ru ∨ s = .J4) →
      Subgroup.center X = ⊥ ∨ (s = .M22 ∧ Nat.card (Subgroup.center X) = 3)

theorem k_J1IsCenterless_holds :
    ∀ (X : Type) [Group X] [Finite X],
      CFSG.Open.IsQuasisimple X → Odd (Nat.card (Subgroup.center X)) →
      IsSpor (X ⧸ Subgroup.center X) .J1 → Subgroup.center X = ⊥ := by
  rintro X _ _ hq - ⟨eS⟩
  let ε : X ⧸ Subgroup.center X ≃* ↥CFSG.Open.walterJ1 :=
    eS.trans CFSG.Walter.walterJ1EquivNative.symm
  have hker := CFSG.Walter.J1Props.J3_multiplier (CFSG.GH74.Generic.centralQuotientMap ε)
    (CFSG.GH74.Generic.centralQuotientMap_surjective ε)
    (CFSG.GH74.Generic.centralQuotientMap_ker ε).le hq.1
  rwa [CFSG.GH74.Generic.centralQuotientMap_ker ε] at hker

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
