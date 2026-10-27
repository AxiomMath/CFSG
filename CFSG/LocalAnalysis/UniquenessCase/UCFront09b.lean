module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

@[expose] def I9 (H : Subgroup G) : Subgroup G := (CFSG.pPrimeCore 3 ↥H).map H.subtype

@[expose] def L9 (Y H : Subgroup G) : Subgroup G :=
  ⨆ h : ↥H, (Opp 3 Y).map (MulAut.conj (h : G)).toMonoidHom

abbrev Hbar9 (H : Subgroup G) : Type := ↥H ⧸ CFSG.pPrimeCore 3 ↥H

@[expose] def img9 (H K : Subgroup G) : Subgroup (Hbar9 H) :=
  (K.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H))

abbrev Lbar9 (Y H : Subgroup G) : Type := ↥(img9 H (L9 Y H))

abbrev BarO3 (X : Subgroup G) : Type := ↥X ⧸ CFSG.pPrimeCore 3 ↥X

@[expose] def InvStar9 (K X : Subgroup G) (p : ℕ) : Set (Subgroup G) :=
  {R | Maximal (· ∈ Inv9 K X p) R}

@[expose] def Shape92 (L : Type) [Group L] : Prop :=
  (IsCyclic L ∧ IsPGroup 3 L) ∨ IsSpor L .J1 ∨ (∃ p f : ℕ, LieModel L .PSL 2 p f) ∨
    (∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel L .PSL 3 p f) ∨
    (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel L .PSU 3 p f)

@[expose] def IsSL2Cover (Q : Type) [Group Q] (p e : ℕ) : Prop :=
  IsQuasisimple Q ∧ Nat.card (center Q) = 2 ∧ LieModel (Q ⧸ center Q) .PSL 2 p e

@[expose] def R92 (D : Data G) : Prop :=
  ∀ Y H D₃ : Subgroup G, Hyp91 D Y H D₃ → H ≠ ⊤ →
    H = L9 Y H ⊔ (H ⊓ D.M) ∧ Shape92 (Lbar9 Y H)

@[expose] def R99 (D : Data G) : Prop :=
  ∀ Y ∈ calY2Star9 D, pCoreOf 2 Y ≠ ⊥ → Fstar Y = pCoreOf 2 Y

@[expose] def R910 (D : Data G) : Prop :=
  ∀ Y ∈ calY2Star9 D, ∀ B : Subgroup G, B ≠ ⊥ → B ≤ Y → (B.subgroupOf Y).Normal →
    (∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S Y ∧
      ¬ CFSG.ABGLocalTools.IsSylowOf 2 S (D.M ⊓ normalizer (B : Set G))) →
    UniqueMax D.M (D.M ⊓ normalizer (B : Set G))

@[expose] def R911 (D : Data G) : Prop :=
  ∀ Y ∈ calY2Star9 D, ¬ CFSG.RankThree.PartOne.InClassX ↥(Opp 3 Y)

@[expose] def R9R5 (D : Data G) : Prop :=
  ∀ Y H D₃ S : Subgroup G, Hyp97 D Y H D₃ S →
    ((Opp 3 Y).subgroupOf (H ⊓ D.M)).Normal ∧ CFSG.ABGLocalTools.IsSylowOf 2 S (H ⊓ D.M)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
