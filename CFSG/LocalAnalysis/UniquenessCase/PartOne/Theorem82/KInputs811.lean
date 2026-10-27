module

public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811CoordDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
open scoped Pointwise commutatorElement

@[expose] def innAut (Y : Type) [Group Y] : Subgroup (MulAut Y) :=
  (MulAut.conj : Y →* MulAut Y).range

inductive LieFam811 where
  | psp6
  | omega7
  | pomega8m
  | l4
  | l6
  | l7
  deriving DecidableEq

@[expose] def IsLieFam811 (X : Type) [Group X] : LieFam811 → ℕ → ℕ → Prop
  | .psp6, r, f => r.Prime ∧ r ≠ 3 ∧ LieModel X .PSp 3 r f
  | .omega7, r, f => r.Prime ∧ r ≠ 2 ∧ r ≠ 3 ∧ LieModel X .POmegaOdd 3 r f
  | .pomega8m, r, f => r.Prime ∧ r ≠ 3 ∧ LieModel X .POmegaMinus 4 r f
  | .l4, r, f => r.Prime ∧ r ^ f ≠ 2 ∧
      ((r ^ f % 3 = 1 ∧ LieModel X .PSL 4 r f) ∨
        (r ^ f % 3 = 2 ∧ LieModel X .PSU 4 r f))
  | .l6, r, f => r.Prime ∧
      ((r ^ f % 3 = 2 ∧ LieModel X .PSL 6 r f) ∨
        (r ^ f % 3 = 1 ∧ LieModel X .PSU 6 r f))
  | .l7, r, f => r.Prime ∧
      ((r ^ f % 3 = 2 ∧ LieModel X .PSL 7 r f) ∨
        (r ^ f % 3 = 1 ∧ LieModel X .PSU 7 r f))

@[expose] def IsLie811 (Y : Type) [Group Y] (fam : LieFam811) (r f : ℕ) : Prop :=
  IsQuasisimple Y ∧ Odd (Nat.card (center Y)) ∧ IsLieFam811 (Y ⧸ center Y) fam r f

@[expose] def qMinusPi (r f : ℕ) : ℕ := if r ^ f % 3 = 1 then r ^ f - 1 else r ^ f + 1

@[expose] def qPlusPi (r f : ℕ) : ℕ := if r ^ f % 3 = 1 then r ^ f + 1 else r ^ f - 1

@[expose] def K34odd : Prop :=
  ∀ (L : Type) [Group L] [Finite L], CFSG.Open.IsQuasisimple L →
    CFSG.Open.IsCatalogGroup (L ⧸ Subgroup.center L) → Odd (Nat.card (Subgroup.center L)) →
    CFSG.Open.pRank 3 (⊤ : Subgroup L) = 3 →
      ThreeCover (fun Y _ => IsSpor Y .ONan) L ∨
      (¬ 3 ∣ Nat.card (Subgroup.center L) ∧
        (
        (IsAlt (L ⧸ Subgroup.center L) 9 ∨ IsAlt (L ⧸ Subgroup.center L) 10 ∨
          IsAlt (L ⧸ Subgroup.center L) 11) ∨
        (LieModel (L ⧸ Subgroup.center L) .PSL 2 3 3 ∨
          LieModel (L ⧸ Subgroup.center L) .PSp 2 3 1) ∨
        ((∃ p f : ℕ, p ≠ 3 ∧ LieModel (L ⧸ Subgroup.center L) .PSp 3 p f) ∨
          (∃ p f : ℕ, p ≠ 3 ∧ LieModel (L ⧸ Subgroup.center L) .POmegaMinus 4 p f) ∨
          (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel (L ⧸ Subgroup.center L) .PSL 4 p f) ∨
          (∃ p f : ℕ, p ^ f % 3 = 2 ∧ p ^ f ≠ 2 ∧
            LieModel (L ⧸ Subgroup.center L) .PSU 4 p f) ∨
          (∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel (L ⧸ Subgroup.center L) .PSL 6 p f) ∨
          (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel (L ⧸ Subgroup.center L) .PSU 6 p f) ∨
          (∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel (L ⧸ Subgroup.center L) .PSL 7 p f) ∨
          (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel (L ⧸ Subgroup.center L) .PSU 7 p f) ∨
          (∃ p f : ℕ, p ≠ 3 ∧ LieModel (L ⧸ Subgroup.center L) .POmegaOdd 3 p f)) ∨
        IsSpor (L ⧸ Subgroup.center L) .J3))

@[expose] def K1 : Prop := K34odd

@[expose] def K2 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsQuasisimple Y → IsCatalogGroup (Y ⧸ center Y) →
    Odd (Nat.card (center Y)) → pRank 3 (⊤ : Subgroup Y) = 3 →
    ¬ ThreeCover (fun Z _ => IsSpor Z .ONan) Y → ¬ LieModel (Y ⧸ center Y) .PSL 2 3 3 →
    ∀ R : Subgroup (MulAut Y), IsPGroup 3 R →
      CFSG.ABGLocalTools.IsSylowOf 3 (R ⊓ innAut Y) (innAut Y) → ¬ R ≤ innAut Y →
      4 ≤ pRank 3 R

@[expose] def K3 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], ThreeCover (fun Z _ => IsSpor Z .ONan) Y →
    ∀ S : Sylow 3 Y, Nat.card S = 3 ^ 5 ∧ (∀ x ∈ (S : Subgroup Y), x ^ 3 = 1) ∧
      Nat.card ↥((S : Subgroup Y) ⊓ (centralizer (S : Set Y) : Subgroup Y)) = 3 ∧
      ⁅(S : Subgroup Y), (S : Subgroup Y)⁆ =
        (S : Subgroup Y) ⊓ (centralizer (S : Set Y) : Subgroup Y)

@[expose] def K3Exp : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], ThreeCover (fun Z _ => IsSpor Z .ONan) Y →
    ∀ S : Sylow 3 Y, ∀ x ∈ (S : Subgroup Y), x ^ 3 = 1

theorem k3Exp_of_k3 (h : K3) : K3Exp := fun Y _ _ hY S => (h Y hY S).2.1

@[expose] def K3Out : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], ThreeCover (fun Z _ => IsSpor Z .ONan) Y →
    ∀ φ : MulAut Y, IsPGroup 3 (Subgroup.zpowers φ) → φ ∈ innAut Y

@[expose] def K4a : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsQuasisimple Y → Odd (Nat.card (center Y)) →
    LieModel (Y ⧸ center Y) .PSL 2 3 3 →
      Nat.card Y = 2 ^ 2 * 3 ^ 3 * 7 * 13 ∧ Nat.card (MulAut Y) = 6 * Nat.card Y ∧
      (∀ φ ψ : MulAut Y, φ * ψ * φ⁻¹ * ψ⁻¹ ∈ innAut Y) ∧
      (∀ p : ℕ, p.Prime → 5 ≤ p → pRank p (⊤ : Subgroup (MulAut Y)) ≤ 1)

@[expose] def K4b : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsQuasisimple Y → Odd (Nat.card (center Y)) →
    LieModel (Y ⧸ center Y) .PSL 2 3 3 →
      (∀ S : Sylow 3 Y, IsElemAbelian 3 (S : Subgroup Y) ∧ Nat.card S = 27) ∧
      ∀ B : Subgroup (MulAut Y), innAut Y ≤ B → 3 ∣ (innAut Y).relIndex B →
      ∀ R : Subgroup (MulAut Y), CFSG.ABGLocalTools.IsSylowOf 3 R B →
        Nat.card R = 81 ∧ IsElemAbelian 3 (R ⊓ innAut Y) ∧
        Nat.card ↥(R ⊓ innAut Y) = 27 ∧
        (∀ E : Subgroup (MulAut Y), E ≤ R → IsElemAbelian 3 E → Nat.card E = 27 →
          E = R ⊓ innAut Y) ∧
        (∃ y ∈ R, y ∉ innAut Y ∧ orderOf y = 3) ∧
        Nat.card ↥(R ⊓ centralizer (R : Set (MulAut Y))) = 3 ∧
        ∀ y ∈ R, y ∉ innAut Y → orderOf y = 3 →
          R ⊓ innAut Y ⊓ centralizer {y} = R ⊓ centralizer (R : Set (MulAut Y)) ∧
          Nat.card ↥(R ⊓ centralizer {y}) = 9 ∧
          (∃ s ∈ R ⊓ innAut Y, ⁅y, ⁅y, s⁆⁆ ≠ 1) ∧
          (∀ x : MulAut Y, y⁻¹ * x ∈ R ⊓ innAut Y → orderOf x = 3 →
            ∃ s ∈ R ⊓ innAut Y, x = s * y * s⁻¹) ∧
          Nat.card {x : MulAut Y // y⁻¹ * x ∈ R ⊓ innAut Y ∧ orderOf x = 3} = 9

@[expose] def K4 : Prop := K4a ∧ K4b ∧ (∀ (Y : Type) [Group Y] [Finite Y], IsQuasisimple Y → Odd
    (Nat.card (center Y)) → LieModel (Y ⧸ center Y) .PSL 2 3 3 → ∀ B : Subgroup (MulAut Y), innAut Y
    ≤ B → ∀ S : Subgroup (MulAut Y), CFSG.ABGLocalTools.IsSylowOf 3 S (innAut Y) → ∀ s ∈ S, s ≠ 1 →
    IsPGroup 3 ↥(B ⊓ centralizer {s}) ∧ (Nat.card ↥(B ⊓ centralizer {s}) = Nat.card S ∨
    CFSG.ABGLocalTools.IsSylowOf 3 (B ⊓ centralizer {s}) B) ∧ (CFSG.ABGLocalTools.IsSylowOf 3 (B ⊓
    centralizer {s}) B ↔ ∃ R' : Subgroup (MulAut Y), CFSG.ABGLocalTools.IsSylowOf 3 R' B ∧ S ≤ R' ∧
    R' ≤ centralizer {s}))

@[expose] def K5A9 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsQuasisimple Y → Odd (Nat.card (center Y)) →
    IsAlt (Y ⧸ center Y) 9 → ∀ p : ℕ, p.Prime → 5 ≤ p →
      pRank p (⊤ : Subgroup (MulAut Y)) ≤ 1

@[expose] def K5A10 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsQuasisimple Y → Odd (Nat.card (center Y)) →
    IsAlt (Y ⧸ center Y) 10 → ∀ p : ℕ, p.Prime → 5 ≤ p →
      pRank p (⊤ : Subgroup (MulAut Y)) ≤ 2

@[expose] def K5A11 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsQuasisimple Y → Odd (Nat.card (center Y)) →
    IsAlt (Y ⧸ center Y) 11 → ∀ p : ℕ, p.Prime → 5 ≤ p →
      pRank p (⊤ : Subgroup (MulAut Y)) ≤ 2

@[expose] def K5J3 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsQuasisimple Y → Odd (Nat.card (center Y)) →
    IsSpor (Y ⧸ center Y) .J3 → ∀ p : ℕ, p.Prime → 5 ≤ p →
      pRank p (⊤ : Subgroup (MulAut Y)) ≤ 1

@[expose] def K5ONan : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], ThreeCover (fun Z _ => IsSpor Z .ONan) Y →
    ∀ p : ℕ, p.Prime → 5 ≤ p →
      pRank p (⊤ : Subgroup (MulAut Y)) ≤ 2

@[expose] def K5U42 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsQuasisimple Y → Odd (Nat.card (center Y)) →
    LieModel (Y ⧸ center Y) .PSp 2 3 1 → ∀ p : ℕ, p.Prime → 5 ≤ p →
      pRank p (⊤ : Subgroup (MulAut Y)) ≤ 1

@[expose] def K5L227 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsQuasisimple Y → Odd (Nat.card (center Y)) →
    LieModel (Y ⧸ center Y) .PSL 2 3 3 → ∀ p : ℕ, p.Prime → 5 ≤ p →
      pRank p (⊤ : Subgroup (MulAut Y)) ≤ 1

@[expose] def K5 : Prop := K5A9 ∧ K5A10 ∧ K5A11 ∧ K5J3 ∧ K5ONan ∧ K5U42 ∧ K5L227

@[expose] def K6a : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], ∀ (fam : LieFam811) (r f : ℕ), IsLie811 Y fam r f →
    ∀ P : Sylow 3 Y, ∃! A : Subgroup Y, A ≤ P ∧ IsElemAbelian 3 A ∧ Nat.card A = 27

@[expose] def K6b : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], ∀ (fam : LieFam811) (r f : ℕ), IsLie811 Y fam r f →
    ∀ A : Subgroup Y, IsElemAbelian 3 A → Nat.card A = 27 →
      ∀ x : Y, orderOf x = 3 → ∃ g : Y, g * x * g⁻¹ ∈ A

@[expose] def K6c : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], ∀ (fam : LieFam811) (r f : ℕ), IsLie811 Y fam r f →
    ∀ A : Subgroup Y, IsElemAbelian 3 A → Nat.card A = 27 →
      (fam = .l4 → ∃ c, IsSumZeroCoords A c) ∧ (fam ≠ .l4 → ∃ c, IsSignedCoords A c)

@[expose] def K6d : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], ∀ (fam : LieFam811) (r f : ℕ), IsLie811 Y fam r f →
    ∀ A : Subgroup Y, IsElemAbelian 3 A → Nat.card A = 27 →
      IsMulCommutative ↥(centralizer (A : Set Y))

@[expose] def K6dL4 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (r : ℕ), IsLie811 Y .l4 r 1 → 5 ≤ r →
    ∀ A : Subgroup Y, IsElemAbelian 3 A → Nat.card A = 27 →
      IsMulCommutative ↥(centralizer (A : Set Y))

theorem k6dL4_of_k6d (h : K6d) : K6dL4 := fun Y _ _ r hY _ => h Y .l4 r 1 hY

@[expose] def K6r : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], ∀ (fam : LieFam811) (r f : ℕ), IsLie811 Y fam r f →
    5 ≤ r → ¬ (fam = .l4 ∧ f = 1) →
    ∀ A : Subgroup Y, IsElemAbelian 3 A → Nat.card A = 27 →
      (∀ X : Subgroup Y, X ≤ A → Nat.card X = 3 →
        2 ≤ pRank r (centralizer (X : Set Y))) ∧
      (fam ≠ .l4 → ∀ c, IsSignedCoords A c →
        1 ≤ pRank r (centralizer ({c (.ofAdd ![1, 0, 0]),
          c (.ofAdd ![0, 1, 0])} : Set Y)) ∧
        1 ≤ pRank r (centralizer ({c (.ofAdd ![1, 1, 1]),
          c (.ofAdd ![0, 0, 1])} : Set Y))) ∧
      (fam = .l4 → ∀ c, IsSumZeroCoords A c →
        1 ≤ pRank r (centralizer ({c (.ofAdd ![1, 1, -1, -1]),
          c (.ofAdd ![1, -1, 0, 0])} : Set Y)))

@[expose] def K6L4 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], ∀ r : ℕ, IsLie811 Y .l4 r 1 → 5 ≤ r →
    (∀ φ : MulAut Y, ∃ k : ℕ, φ ^ (2 ^ k) ∈ innAut Y) ∧
    ∀ A : Subgroup Y, IsElemAbelian 3 A → Nat.card A = 27 → ∀ c, IsSumZeroCoords A c →
      (∀ X : Subgroup Y, X ≤ A → Nat.card X = 3 →
        r ∣ Nat.card (centralizer (X : Set Y))) ∧
      (Nat.card (centralizer ({c (.ofAdd ![1, 1, -1, -1])} : Set Y))).factorization r = 2 ∧
      (Nat.card (centralizer ({c (.ofAdd ![1, -1, 0, 0])} : Set Y))).factorization r = 1 ∧
      (Nat.card (centralizer ({c (.ofAdd ![1, 1, 1, 0])} : Set Y))).factorization r = 3 ∧
      pRank r (centralizer ({c (.ofAdd ![1, 1, -1, -1])} : Set Y)) = 2 ∧
      pRank r (centralizer ({c (.ofAdd ![1, 1, 1, 0])} : Set Y)) = 2 ∧
      (∀ Q : Subgroup Y, CFSG.ABGLocalTools.IsSylowOf 3 Q (centralizer (A : Set Y)) →
        CFSG.ABGLocalTools.IsSylowOf 3 Q
          (centralizer ({c (.ofAdd ![1, -1, 0, 0])} : Set Y))) ∧
      (∃ K : Subgroup Y, K ≤ centralizer ({c (.ofAdd ![1, 1, -1, -1])} : Set Y) ∧
        ¬ IsSolvable ↥K ∧ ⁅K, K⁆ = K ∧ Nat.card K = r ^ 2 * (r ^ 2 - 1) ^ 2 / 2 ∧
        ∀ N : Subgroup Y, N ≤ K → (N.subgroupOf K).Normal → Odd (Nat.card N) → N = ⊥) ∧
      (∃ K : Subgroup Y, K ≤ centralizer ({c (.ofAdd ![1, 1, 1, 0])} : Set Y) ∧
        ¬ IsSolvable ↥K ∧
        ∀ N : Subgroup Y, N ≤ K → (N.subgroupOf K).Normal → Odd (Nat.card N) →
          N ≤ centralizer (K : Set Y))

@[expose] def K6Z : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], ∀ (fam : LieFam811) (r f : ℕ), IsLie811 Y fam r f → 5 ≤ r →
    ¬ r ∣ Nat.card (center Y)

@[expose] def K6ZL4 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (r : ℕ), IsLie811 Y .l4 r 1 → 5 ≤ r →
    ¬ r ∣ Nat.card (center Y)

theorem k6ZL4_of_k6Z (h : K6Z) : K6ZL4 := fun Y _ _ r hY hr => h Y .l4 r 1 hY hr

@[expose] def K6 : Prop := K6a ∧ K6b ∧ K6c ∧ K6d ∧ K6r ∧ K6L4

@[expose] def K7 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], ∀ (fam : LieFam811) (r f : ℕ), IsLie811 Y fam r f →
    ∀ p : ℕ, p.Prime → 5 ≤ p → p ≠ r →
    ∀ A : Subgroup Y, IsElemAbelian 3 A → Nat.card A = 27 →
      (p ∣ qMinusPi r f → 2 ≤ pRank p (centralizer (A : Set Y))) ∧
      (p ∣ qPlusPi r f →
        ((fam = .l6 ∨ fam = .l7) → 2 ≤ pRank p (centralizer (A : Set Y))) ∧
        (fam = .l4 → pRank p (⊤ : Subgroup Y) ≤ 2) ∧
        ((fam = .psp6 ∨ fam = .omega7) →
          ¬ p ∣ Nat.card (centralizer (A : Set Y)) ∧
          (∀ X : Subgroup Y, X ≤ A → Nat.card X = 3 →
            p ∣ Nat.card (centralizer (X : Set Y))) ∧
          pRank p (⊤ : Subgroup Y) ≤ 3) ∧
        (fam = .pomega8m →
          ∃ y ∈ centralizer (A : Set Y), orderOf y = p ∧
            ∀ X : Subgroup Y, X ≤ A → Nat.card X = 3 →
              ∃ u ∈ centralizer (X : Set Y), orderOf u = p ∧ u * y = y * u ∧
                u ∉ zpowers y)) ∧
      (¬ p ∣ r ^ f * (r ^ (2 * f) - 1) → pRank p (⊤ : Subgroup Y) ≤ 2)

@[expose] def K8 : Prop := CFSG.LocalAnalysis.UniquenessCase.UCK.K35

@[expose] def K9 : Prop := CFSG.LocalAnalysis.UniquenessCase.UCK.K332

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
