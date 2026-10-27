module

public import CFSG.RankThree.PartTwo.Sec21.Item22Statements

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaMinus)
open CFSG.Assembly (IsElemAbelian)

variable {G : Type} [Group G]

structure IsChainSystem (r : ℕ) (E : Subgroup G) (K : Fin r → Subgroup G) : Prop where
  commute : ∀ i j : Fin r, i.val + 1 < j.val → ∀ x ∈ K i, ∀ y ∈ K j, x * y = y * x
  inf_eq_bot : ∀ i j : Fin r, i.val + 1 < j.val → K i ⊓ K j = ⊥
  elem : IsElemAbelian 3 E
  le : E ≤ ⨆ i, K i
  split : ∀ i, E = (E ⊓ Subgroup.centralizer (K i : Set G)) ⊔ (E ⊓ K i)
  index : ∀ i, Nat.card E = 3 * Nat.card (E ⊓ Subgroup.centralizer (K i : Set G) : Subgroup G)
  index₂ : ∀ i j, i ≠ j → Nat.card E =
    9 * Nat.card (E ⊓ Subgroup.centralizer ((K i ⊔ K j : Subgroup G) : Set G) : Subgroup G)

@[expose] def IsSLThree (Y : Subgroup G) (n : ℕ) : Prop :=
  Nonempty (Y ≃* SL3 n) ∨ Nonempty (Y ≃* projSL 3 (GaloisField 2 n))

@[expose] def IsSUThree (Y : Subgroup G) (n : ℕ) : Prop :=
  Nonempty (Y ≃* SU3 n) ∨ Nonempty (Y ≃* projSU 3 2 n)

@[expose] def CurtisTitsRankThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (E : Subgroup G) (K : Fin 3 → Subgroup G) (m : ℕ),
    0 < m → Even m → IsChainSystem 3 E K →
    ((∀ i, Nonempty (K i ≃* projSL 2 (GaloisField 2 m))) → IsSLThree (K 0 ⊔ K 1) m →
        IsSLThree (K 1 ⊔ K 2) m →
        Nonempty ((⨆ i, K i : Subgroup G) ⧸ Subgroup.center (⨆ i, K i : Subgroup G) ≃*
          projSL 4 (GaloisField 2 m))) ∧
    ((∀ i, Nonempty (K i ≃* projSL 2 (GaloisField 2 m))) → IsSLThree (K 0 ⊔ K 1) m →
        Nonempty ((K 1 ⊔ K 2 : Subgroup G) ≃* projSp 2 (GaloisField 2 m)) →
        Nonempty ((⨆ i, K i : Subgroup G) ⧸ Subgroup.center (⨆ i, K i : Subgroup G) ≃*
          projSp 3 (GaloisField 2 m))) ∧
    (Nonempty (K 0 ≃* projSL 2 (GaloisField 2 m)) →
        Nonempty (K 1 ≃* projSL 2 (GaloisField 2 m)) →
        Nonempty (K 2 ≃* projSL 2 (GaloisField 2 (2 * m))) → IsSLThree (K 0 ⊔ K 1) m →
        Nonempty ((K 1 ⊔ K 2 : Subgroup G) ≃* projSU 4 2 m) →
        ¬ E ⊓ K 1 ≤ Subgroup.centralizer (K 2 : Set G) →
        ∃ b c : GaloisField 2 m, (∀ s : GaloisField 2 m, s ^ 2 + b * s + c ≠ 0) ∧
          Nonempty ((⨆ i, K i : Subgroup G) ⧸ Subgroup.center (⨆ i, K i : Subgroup G) ≃*
            projOmegaMinus 3 (GaloisField 2 m) b c)) ∧
    (Nonempty (K 0 ≃* projSL 2 (GaloisField 2 (2 * m))) →
        Nonempty (K 1 ≃* projSL 2 (GaloisField 2 (2 * m))) →
        Nonempty (K 2 ≃* projSL 2 (GaloisField 2 m)) → IsSLThree (K 0 ⊔ K 1) (2 * m) →
        Nonempty ((K 1 ⊔ K 2 : Subgroup G) ≃* projSU 4 2 m) →
        ¬ E ⊓ K 2 ≤ Subgroup.centralizer (K 1 : Set G) →
        Nonempty ((⨆ i, K i : Subgroup G) ⧸ Subgroup.center (⨆ i, K i : Subgroup G) ≃*
          projSU 6 2 m))

@[expose] def PhanChain : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (r : ℕ) (E : Subgroup G) (K : Fin r → Subgroup G) (m : ℕ),
    2 < r → 1 < m → Odd m → IsChainSystem r E K →
    (∀ i, Nonempty (K i ≃* projSL 2 (GaloisField 2 m))) →
    (∀ i j : Fin r, i.val + 1 = j.val → IsSUThree (K i ⊔ K j) m) →
    Nonempty ((⨆ i, K i : Subgroup G) ⧸ Subgroup.center (⨆ i, K i : Subgroup G) ≃*
      projSU (r + 1) 2 m)

end CFSG.RankThree.PartTwo.Sec21
