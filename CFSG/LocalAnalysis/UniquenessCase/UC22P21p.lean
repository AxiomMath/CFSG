module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront11

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup F11

variable {G : Type} [Group G] [Finite G]

@[expose] def C119 (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ [((CTilde D.M V₀ V).subgroupOf D.M).Normal] (X : Subgroup G),
    CTilde D.M V₀ V ≤ X → X ≤ D.M →
    rankThreeLayer (barImage11 D.M V₀ V X) = barImage11 D.M V₀ V X →
    ∃ Y : Subgroup G, IsY119 D.M V₀ V X Y ∧
      ((∃ Lbar : Subgroup (MBar11 D.M V₀ V), IsComponentOf Lbar ⊤ ∧
          barImage11 D.M V₀ V X =
            ⨆ g : MBar11 D.M V₀ V, Lbar.map (MulAut.conj g).toMonoidHom) →
        ¬ F09.Thin9 Y → ⁅Y, V₀⁆ = ⊥)

@[expose] def R119W (D : Data G) : Prop := ∀ V : Subgroup G, Hyp11 D ⊥ V → C119 D ⊥ V

theorem r119W_of_r119 (D : Data G) (h : R119 D) : R119W D := fun V hV => h ⊥ V hV

@[expose] def R1110W (D : Data G) : Prop :=
  ∀ V : Subgroup G, Hyp11 D ⊥ V →
    ∀ [((CTilde D.M ⊥ V).subgroupOf D.M).Normal],
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p P (O2p p D.M) →
      pCoreOf p ⁅(⊤ : Subgroup (MBar11 D.M ⊥ V)), ⊤⁆ = barImage11 D.M ⊥ V (P ⊓ ⁅D.M, D.M⁆) ∧
      (IsCyclic ↥(P ⊓ CTilde D.M ⊥ V) ∧ ⁅P ⊓ ⁅D.M, D.M⁆, P ⊓ CTilde D.M ⊥ V⁆ = ⊥) ∧
      ∀ n : ℕ, 1 < n → ∀ Xbar : Subgroup (MBar11 D.M ⊥ V), Xbar.Normal →
        IsElemAbelian p Xbar → Nat.card Xbar = p ^ n →
        Xbar ≤ ⁅(⊤ : Subgroup (MBar11 D.M ⊥ V)), ⊤⁆ →
        ((∀ x ∈ Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ barPreimage11 D.M ⊥ V Xbar), x ^ p = 1) ∧
          (IsMulCommutative (Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ barPreimage11 D.M ⊥ V Xbar)) ∨
            (Nat.card ↥⁅Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ barPreimage11 D.M ⊥ V Xbar),
                Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ barPreimage11 D.M ⊥ V Xbar)⁆ = p ∧
              ⁅Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ barPreimage11 D.M ⊥ V Xbar),
                Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ barPreimage11 D.M ⊥ V Xbar)⁆ ≤
                Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ barPreimage11 D.M ⊥ V Xbar) ⊓
                  centralizer ((Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ barPreimage11 D.M ⊥ V Xbar) :
                    Subgroup G) : Set G))) ∧
          p ^ n ≤ Nat.card (Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ barPreimage11 D.M ⊥ V Xbar)) ∧
          n / 2 + 1 ≤ CFSG.Open.pRank p (Omega1p p (P ⊓ ⁅D.M, D.M⁆ ⊓ barPreimage11 D.M ⊥ V Xbar))) ∧
        (D.sig = D.sig1 → ∀ v ∈ V, v ≠ 1 →
          1 < CFSG.Open.pRank p (Xbar ⊓ barImage11 D.M ⊥ V (CElt D.M ⊥ v)) →
            UniqueMax D.M (D.M ⊓ centralizer ({v} : Set G)))

end CFSG.LocalAnalysis.UniquenessCase.UC22
