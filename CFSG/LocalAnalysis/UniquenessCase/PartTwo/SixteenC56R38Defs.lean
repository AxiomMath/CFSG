module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16c
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB
public import CFSG.LocalAnalysis.UniquenessCase.UC22DataExt
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def R16_38_rankGap (D : Data G) : Prop :=
  UC6S846.SigmaStd D → D.sig = D.sig1 → R1621 D → R1622 D → UC6.R6_1 D → DataExt D →
    R16_5 D →
    ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
      ∀ m : ℕ, Case1633 D V₀ V hV L m → ∀ n : ℕ, n + 2 ≤ 2 * m → ∀ g : G,
        InCalOStar n D.M V₀ V g → (2 ^ m - 1).Prime →
          ∀ (a : MulAut (Vtil V₀ V hV)) (E : Subgroup (MulAut (Vtil V₀ V hV))), a ∈ E →
            a ∈ Mbar D.M V₀ V hV → E ≤ lBar V₀ V hV L ⊔ Subgroup.zpowers a →
            (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ (2 ^ m - 1) = 1) →
            Nat.card E = (2 ^ m - 1) ^ 3 → 3 ≤ CFSG.Open.pRank (2 ^ m - 1) D.M

@[expose] def R16_38_m3Gap (D : Data G) : Prop :=
  UC6S846.SigmaStd D → D.sig = D.sig1 → R1621 D → R1622 D → UC6.R6_1 D → DataExt D →
    R16_5 D →
    ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
      Case167_6 D V₀ V hV L → ∀ n : ℕ, n + 2 ≤ 2 * 3 → ∀ g : G, InCalOStar n D.M V₀ V g →
        CFSG.Open.evenRank G ≠ 3 → 3 ≤ CFSG.Open.pRank 7 D.M → False

@[expose] def R16_38_m2Gap (D : Data G) : Prop :=
  UC6S846.SigmaStd D → D.sig = D.sig1 → R1621 D → R1622 D → UC6.R6_1 D → DataExt D →
    R16_5 D → F07.R76Sig D → UC6.R6_14 D →
    ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
      Case167_5 D V₀ V hV L → ∀ n : ℕ, n + 2 ≤ 2 * 2 → ∀ g : G, InCalOStar n D.M V₀ V g →
        3 ≤ CFSG.Open.pRank 3 D.M → False

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
