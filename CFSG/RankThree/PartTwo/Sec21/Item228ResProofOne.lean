module

public import CFSG.RankThree.PartTwo.Sec21.Item2131One
import CFSG.RankThree.PartTwo.Sec13.Item13Plane
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

@[expose] def List228 (Y : Type) [Group Y] (m : ℕ) : Prop :=
  (Nonempty (Y ≃* SL3 m) ∨ Nonempty (Y ≃* projSp 2 (GaloisField 2 m)) ∨
      Nonempty (Y ≃* projSU 4 2 m) ∨ (m % 4 = 0 ∧ Nonempty (Y ≃* projSU 4 2 (m / 2))) ∨
      ((m = 2 ∨ m = 4) ∧ Nonempty (Y ≃* projSU 5 2 2))) ∨
    (m = 2 ∧ StatedClassicalModel Y .PSp 2 5 1) ∨
    (m = 2 ∧ (StatedClassicalModel Y .PSL 4 2 1 ∨ StatedClassicalModel Y .PSL 5 2 1))

@[expose] def Item228NoFieldThree :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nat.card A = 3 ^ 3 →
      ∀ φ ∈ dStar A, ∀ X ∈ lStar A, kOf A φ ≤ X →
        ∀ x ∈ A, ¬ KFacts.InducesStdKind X x .field ∧ ¬ KFacts.InducesStdKind X x .graphField

@[expose] def Inspection228List :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X A K K₀ : Subgroup G) (m : ℕ),
    Sec4.IsList46 (X ⧸ aschbacherSolvableCore 3 X) →
    Maximal (fun B : Subgroup G => IsElemAbelian 3 B) A → Nat.card A = 3 ^ 3 →
    A ≤ Subgroup.normalizer (X : Set G) →
    Nat.card (A ⊓ Sec4.thetaQuotCentralizer X : Subgroup G) = 3 →
    (∀ x ∈ A, Sec4.InducesOuterTheta x X → KFacts.InducesStdKind X x .diagonal) →
    (∀ ρ ∈ starOf A X, ¬ IsTransvectionOn ρ) →
    ∀ ρ ∈ starOf A X, IsReflectionOn ρ →
      K ≤ K₀ → K₀ ≤ X → K₀ ≤ Subgroup.centralizer (fixedInG A ρ : Set G) →
      (∀ y ∈ X ⊓ Subgroup.centralizer (fixedInG A ρ : Set G), ∀ k ∈ K₀, y * k * y⁻¹ ∈ K₀) →
      (K = K₀ ∨ StatedClassicalModel K₀ .PSU 3 2 2) →
      Nonempty (K ≃* projSL 2 (GaloisField 2 m)) → 0 < m → Even m →
        List228 (X ⧸ aschbacherSolvableCore 3 X) m

@[expose] def Item228ThetaTrivial : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nat.card A = 3 ^ 3 →
      ∀ φ ∈ dStar A, ∀ X ∈ lStar A, kOf A φ ≤ X → ∀ m : ℕ, 0 < m → Even m →
        Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 m)) →
        List228 (X ⧸ aschbacherSolvableCore 3 X) m →
          inSubgroup (aschbacherSolvableCore 3) X = ⊥

namespace Item228ResProof

variable {G : Type} [Group G]

theorem false_of_normalizer_le [Finite G] (h2130 : Item2130) {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) {a : G} (haA : a ∈ A) (ha1 : a ≠ 1)
    (hle : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G)) : False := by
  have hirr : IsIrreducibleOn (Sec4.autIn (Subgroup.normalizer (A : Set G)) A) := by
    rw [Item2131One.autIn_normalizer_eq_wStar]
    exact h2130 G A E U c L hpair
  rcases Sec13.eq_bot_or_eq_of_isIrreducibleOn hirr (Subgroup.zpowers_le.mpr haA) hle with h | h
  · exact ha1 (Subgroup.zpowers_eq_bot.mp h)
  · have hEA : E ≤ A := hpair.mem_E.2
    have hE27 : Nat.card E = 27 := hpair.mem_E.1.2.1
    have ha3 : a ^ 3 = 1 := hpair.mem_S.1.1.2 a haA
    have h1 : Nat.card A ∣ 3 := by
      rw [← h, Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one ha3
    have h2 : 27 ∣ Nat.card A := hE27 ▸ Subgroup.card_dvd_of_le hEA
    have := Nat.le_of_dvd (by norm_num) (h2.trans h1)
    omega

end Item228ResProof

open Item228ResProof

variable {G : Type} [Group G]

end CFSG.RankThree.PartTwo.Sec21
