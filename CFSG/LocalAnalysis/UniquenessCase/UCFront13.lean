module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.UniquenessCase.UCFront12
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F13

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def Thin13 (L : Subgroup G) : Prop :=
  ∀ r : ℕ, r.Prime → r ≠ 2 → CFSG.Open.pRank r L ≤ 1

@[expose] def OTwoEIn (M : Subgroup G) : Subgroup G :=
  (OTwoE ↥M).map M.subtype

@[expose] def cMStar (M X : Subgroup G) : Subgroup G :=
  ((centralizer (((X.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) :
    Subgroup (Bar2 M)) : Set (Bar2 M))).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype

@[expose] def Lp (M : Subgroup G) (p : ℕ) : Subgroup G :=
  Opp p (OTwoEIn M)

@[expose] def Sp (M : Subgroup G) (p : ℕ) : Subgroup G :=
  Opp p (cMStar M (Lp M p))

structure Hyp131 (D : Data G) : Prop where
  thinOrU3 : ∀ L ∈ calC D.M, Thin13 L ∨ ∃ n : ℕ, (∃ k : ℕ, n = 2 ^ k) ∧ IsU3 (Bar2 L) n
  normal : ∀ L ∈ calC D.M, (L.subgroupOf D.M).Normal
  layer : CFSG.perfectResidual (Bar2 D.M) = CFSG.layer (Bar2 D.M)
  uniq : ∀ L ∈ calC D.M, ∀ n : ℕ, (IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n) →
    ∀ s : ℕ, Odd s → s ∣ n → ∀ r : ℕ, r.Prime → r ∣ 2 ^ s - 1 →
      ∀ X : Subgroup G, X ≤ L → Nat.card X = r →
        normalizer (X : Set G) ≤ D.M ∧ X ∉ uniqueSet D.M
  smallS : ∀ p ∈ D.sig, CFSG.Open.pRank p (Sp D.M p) ≤ 1
  notAmong : ∀ L ∈ calC D.M,
    (IsJ1 (Bar2 L) ∨ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 5 < p ^ f ∧
      CFSG.Blueprint.LieModel (Bar2 L) .PSL 2 p f) →
    ∀ K ∈ calC D.M, K ≠ L →
      ¬ ((∃ n : ℕ, IsL2 (Bar2 K) (2 ^ n)) ∨ (∃ n : ℕ, IsU3 (Bar2 K) n) ∨
        (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ IsL2Odd (Bar2 K) p) ∨ IsJ1 (Bar2 K))

@[expose] def Case136a (D : Data G) : Prop :=
  ∃ V₀ V : Subgroup G, Hyp125 D V₀ V ∧ (Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)

@[expose] def Case136b (D : Data G) (p : ℕ) (B : Subgroup G) : Prop :=
  B ≠ ⊥ ∧ B ≤ D.M ∧ Odd (Nat.card B) ∧ Permutes B D.T ∧ ¬ normalizer (B : Set G) ≤ D.M ∧
    ∃ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf p P (Sp D.M p) ∧ P ≤ normalizer (B : Set G)

@[expose] def Concl136 (D : Data G) (p n : ℕ) : Prop :=
  (((∃ (A B : Type) (_ : Group A) (_ : Group B), IsL2 A n ∧ IsL2 B n ∧
        Nonempty (Bar2 (Lp D.M p) ≃* A × B)) ∧ Sp D.M p ≠ ⊥) ∨
    ((∃ (A B : Type) (_ : Group A) (_ : Group B), IsL2 A n ∧ IsU3 B n ∧
        Nonempty (Bar2 (Lp D.M p) ≃* A × B)) ∧ Sp D.M p = ⊥)) ∧
  (∃ k : ℕ, n = 2 ^ k) ∧ p ∣ 2 ^ n + 1

end CFSG.LocalAnalysis.UniquenessCase.UC22.F13
