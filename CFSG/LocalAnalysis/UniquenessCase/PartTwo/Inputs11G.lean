module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront11

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup F11

variable {G : Type} [Group G] [Finite G]

@[expose] def R1110G (D : Data G) : Prop :=
  ∀ V₀ V : Subgroup G, Hyp11 D V₀ V →
    ∀ [((CTilde D.M V₀ V).subgroupOf D.M).Normal],
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf p P (O2p p D.M) →
      pCoreOf p ⁅(⊤ : Subgroup (MBar11 D.M V₀ V)), ⊤⁆ =
          barImage11 D.M V₀ V (P ⊓ ⁅D.M, D.M⁆) ∧
      (IsCyclic ↥(P ⊓ CTilde D.M V₀ V) ∧ ⁅P ⊓ ⁅D.M, D.M⁆, P ⊓ CTilde D.M V₀ V⁆ = ⊥) ∧
      ∀ n : ℕ, 1 < n → ∀ Xbar : Subgroup (MBar11 D.M V₀ V), Xbar.Normal →
        IsElemAbelian p Xbar → Nat.card Xbar = p ^ n →
        Xbar ≤ ⁅(⊤ : Subgroup (MBar11 D.M V₀ V)), ⊤⁆ →
        ((∀ x ∈ Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ barPreimage11 D.M V₀ V Xbar), x ^ p = 1) ∧
          (IsMulCommutative (Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ barPreimage11 D.M V₀ V Xbar)) ∨
            (Nat.card ↥⁅Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ barPreimage11 D.M V₀ V Xbar),
                Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ barPreimage11 D.M V₀ V Xbar)⁆ = p ∧
              ⁅Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ barPreimage11 D.M V₀ V Xbar),
                Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ barPreimage11 D.M V₀ V Xbar)⁆ ≤
                Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ barPreimage11 D.M V₀ V Xbar) ⊓
                  centralizer ((Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ barPreimage11 D.M V₀ V Xbar) :
                    Subgroup G) : Set G))) ∧
          p ^ n ≤ Nat.card (Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ barPreimage11 D.M V₀ V Xbar)) ∧
          n / 2 + 1 ≤
            CFSG.Open.pRank p (Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ barPreimage11 D.M V₀ V Xbar))) ∧
        (D.sig = D.sig1 → ∀ v ∈ V, v ≠ 1 →
          1 < CFSG.Open.pRank p (Xbar ⊓ barImage11 D.M V₀ V (CElt D.M V₀ v)) →
            UniqueMax D.M (D.M ⊓ centralizer ({v} : Set G)))

end CFSG.LocalAnalysis.UniquenessCase.UC22
