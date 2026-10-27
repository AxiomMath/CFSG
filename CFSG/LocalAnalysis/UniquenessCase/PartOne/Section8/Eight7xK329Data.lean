module

public import CFSG.Blueprint.Catalog
public import CFSG.Open.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint (LieModel classicalTags)
open CFSG.Open (StatedLieTag)

@[expose] def K329UDatum (S : Type) [Group S] (u : S) : Prop :=
  orderOf u = 3 ∧ ∃ M N : Subgroup S, M ≤ Subgroup.centralizer ({u} : Set S) ∧
    (M.subgroupOf (Subgroup.centralizer ({u} : Set S))).Normal ∧ N ≤ M ∧
    (N.subgroupOf M).Normal ∧ IsPGroup 3 N ∧ ∃ a ∈ N, ∃ b ∈ N, a * b ≠ b * a

@[expose] def K329ZDatum (S : Type) [Group S] (z : S) : Prop :=
  orderOf z = 3 ∧ ∃ M Y : Subgroup S, M ≤ Subgroup.centralizer ({z} : Set S) ∧
    (M.subgroupOf (Subgroup.centralizer ({z} : Set S))).Normal ∧
    ⁅Subgroup.centralizer ({z} : Set S), Subgroup.centralizer ({z} : Set S)⁆ ≤ M ∧
    Y ≤ M ∧ (Y.subgroupOf M).Normal ∧ LieModel ↥Y .PSL 2 2 3

@[expose] def k329U38LocalFactsStatement : Prop :=
  ∀ (X : Type) [Group X] [Finite X], LieModel X .PSU 3 2 3 → ∀ Q : Sylow 3 X,
    (∃ u ∈ (Q : Subgroup X), orderOf u = 3 ∧ Subgroup.centralizer ({u} : Set X) = Q ∧
        ∃ a ∈ (Q : Subgroup X), ∃ b ∈ (Q : Subgroup X), a * b ≠ b * a) ∧
      ∃ z ∈ (Q : Subgroup X), orderOf z = 3 ∧
        LieModel ↥⁅Subgroup.centralizer ({z} : Set X), Subgroup.centralizer ({z} : Set X)⁆
          .PSL 2 2 3

@[expose] def k329ClassicalYStatement : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S →
    ∀ (t : StatedLieTag) (n r e : ℕ), t ∈ classicalTags → LieModel S t n r e → r ≠ 3 →
      ∀ z : S, K329ZDatum S z → r ^ e = 8

@[expose] def k329ClassicalO3Statement : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S →
    ∀ (t : StatedLieTag) (n : ℕ), t ∈ classicalTags → LieModel S t n 2 3 →
      ∀ u : S, K329UDatum S u → t = .PSU ∧ n = 3

@[expose] def k329HeavyTags : Finset StatedLieTag := {.F4, .E6, .twistedE6, .E7, .E8}

@[expose] def k329HeavyRankStatement : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K → ∀ t ∈ k329HeavyTags,
    ∀ (n r e : ℕ), LieModel (K ⧸ Subgroup.center K) t n r e → r ≠ 3 →
      4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K)

@[expose] def k329ExceptionalYStatement : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S →
    ∀ (t : StatedLieTag) (n r e : ℕ), t ∉ classicalTags → t ∉ k329HeavyTags →
      LieModel S t n r e → r ≠ 3 → ∀ z : S, K329ZDatum S z →
        (t = .G2 ∧ r ^ e = 8) ∨ (t = .trialityD4 ∧ r ^ e = 2) ∨ t = .Tits

@[expose] def k329ExceptionalO3Statement : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → LieModel S .G2 0 2 3 →
    ∀ u : S, ¬ K329UDatum S u

@[expose] def k329NineteenFreeStatement : Prop :=
  ∀ (S : Type) [Group S],
    (LieModel S .trialityD4 0 2 1 ∨ LieModel S .Tits 0 2 1) →
      ¬ 19 ∣ Nat.card S

theorem k329CrossCharacteristicTwoCentralizer_of_leaves
    (hCY : k329ClassicalYStatement) (hCO : k329ClassicalO3Statement)
    (hEY : k329ExceptionalYStatement) (hEO : k329ExceptionalO3Statement)
    (h19 : k329NineteenFreeStatement) :
    ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S →
      ∀ (t : StatedLieTag) (n r e : ℕ), t ∉ k329HeavyTags → LieModel S t n r e → r ≠ 3 →
        19 ∣ Nat.card S → ∀ u z : S, K329UDatum S u → K329ZDatum S z → LieModel S .PSU 3 2 3 := by
  intro S _ _ hS t n r e htH hL hr h19S u z hu hz
  have hrp : r.Prime := hL.admissible.1
  have h8 : ∀ {e : ℕ}, r ^ e = 8 → r = 2 ∧ e = 3 := by
    intro e he
    have h2 : r = 2 := by
      have : r ∣ 2 ^ 3 := by
        have hdvd : r ∣ r ^ e := dvd_pow_self r (by rintro rfl; simp at he)
        rw [he] at hdvd; simpa using hdvd
      exact (Nat.prime_dvd_prime_iff_eq hrp Nat.prime_two).mp (hrp.dvd_of_dvd_pow this)
    subst h2
    exact ⟨rfl, Nat.pow_right_injective le_rfl (by simpa using he)⟩
  have h2' : ∀ {e : ℕ}, r ^ e = 2 → r = 2 ∧ e = 1 := by
    intro e he
    have h2 : r = 2 := by
      have hdvd : r ∣ r ^ e := dvd_pow_self r (by rintro rfl; simp at he)
      rw [he] at hdvd
      exact (Nat.prime_dvd_prime_iff_eq hrp Nat.prime_two).mp hdvd
    subst h2
    exact ⟨rfl, Nat.pow_right_injective le_rfl (by simpa using he)⟩
  by_cases ht : t ∈ classicalTags
  · obtain ⟨rfl, rfl⟩ := h8 (hCY S hS t n r e ht hL hr z hz)
    obtain ⟨rfl, rfl⟩ := hCO S hS t n ht hL u hu
    exact hL
  · have hn : n = 0 := by
      rcases hL with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
      · exact absurd h ht
      all_goals exact h
    subst hn
    rcases hEY S hS t 0 r e ht htH hL hr z hz with ⟨rfl, he⟩ | ⟨rfl, he⟩ | rfl
    · obtain ⟨rfl, rfl⟩ := h8 he
      exact absurd hu (hEO S hS hL u)
    · obtain ⟨rfl, rfl⟩ := h2' he
      exact absurd h19S (h19 S (Or.inl hL))
    · have he : r = 2 ∧ e = 1 := by
        rcases hL with ⟨h, -⟩ | ⟨-, h, -⟩ | ⟨-, -, h⟩ | ⟨-, h, -⟩
        · exact absurd h (by decide)
        · exact absurd h (by decide)
        · exact ⟨h.1.2.2.2.1, h.1.2.2.2.2⟩
        · exact absurd h (by decide)
      obtain ⟨rfl, rfl⟩ := he
      exact absurd h19S (h19 S (Or.inr hL))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
