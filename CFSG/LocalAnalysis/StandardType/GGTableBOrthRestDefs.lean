module

public import CFSG.LocalAnalysis.StandardType.GGAssemblyThreeTableB
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryDesc
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeRestCover

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGOrthRestLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  4 ≤ lab.rank ∧ ((lab.tag = .twD ∧ p ∣ 2 ^ lab.n + 1) ∨ (lab.tag = .D ∧ lab.n = 1 ∧ p = 3))

theorem OrthRest.dvd_sq_sub_one {p n : ℕ} (h : p ∣ 2 ^ n + 1 ∨ p ∣ 2 ^ n - 1) :
    p ∣ (2 ^ n) ^ 2 - 1 := by
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have he : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
    obtain ⟨k, hk⟩ : ∃ k, 2 ^ n = k + 1 := ⟨2 ^ n - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel]
    ring_nf
    omega
  rw [he]
  rcases h with h | h
  · exact Dvd.dvd.mul_right h _
  · exact Dvd.dvd.mul_left h _

theorem ggOrthRestLabel_of_rest3 {p : ℕ} {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (hs : LargeEvenSplit p lab) (h : GGTableBRest3 GGTableBOrthLabel p lab) :
    GGOrthRestLabel p lab := by
  obtain ⟨hO, hD⟩ := h
  have hnS : ¬ GGTableBOrthSplitLabel p lab := fun h' =>
    hD (Or.inr (Or.inr (Or.inl h')))
  rcases hO with ⟨ht, hl⟩ | ⟨ht, hl⟩
  · have hl3 : 3 ≤ lab.rank := by
      have := hlab.2
      rw [ht] at this
      exact this
    have hl4 : 4 ≤ lab.rank := by omega
    refine ⟨hl4, Or.inr ⟨ht, ?_⟩⟩
    rcases (largeEvenSplit_D_iff ht).mp hs with h1 | h1
    · exact absurd ⟨Or.inl ht, hl4, h1⟩ hnS
    · exact h1
  · have hl2 : 2 ≤ lab.rank := by
      have := hlab.2
      rw [ht] at this
      exact this
    have hs' := (largeEvenSplit_twD_iff ht).mp hs
    have hl4 : 4 ≤ lab.rank := by
      by_contra hlt
      have hl2' : lab.rank = 2 := by omega
      apply hD
      refine Or.inl (Or.inl (Or.inl (Or.inr (Or.inr ⟨ht, hl2', ?_⟩))))
      rcases hs' with h1 | h1 | ⟨h1, h2⟩
      · exact OrthRest.dvd_sq_sub_one (Or.inl h1)
      · exact OrthRest.dvd_sq_sub_one (Or.inr h1)
      · rw [h1, h2]
        norm_num
    refine ⟨hl4, Or.inl ⟨ht, ?_⟩⟩
    rcases hs' with h1 | h1 | ⟨h1, h2⟩
    · exact h1
    · exact absurd ⟨Or.inr ht, hl4, h1⟩ hnS
    · rw [h1, h2]
      norm_num

namespace OrthRest

abbrev RMinus (K : Type) [Field K] (m : ℕ) (b c : K) : Type :=
  LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))

abbrev RPlus (K : Type) [Field K] (m : ℕ) : Type :=
  LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))

end OrthRest

@[expose] def GGOrthRestAll (P : ℕ → ℕ → (R : Type) → [Group R] → Prop) : Prop :=
  (∀ (K : Type) [Field K] [Finite K] (n m p : ℕ) (b c : K), Nat.card K = 2 ^ n → 3 ≤ m →
    p.Prime → p ∣ 2 ^ n + 1 → (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      P p m (OrthRest.RMinus K m b c)) ∧
  ∀ (K : Type) [Field K] [Finite K] (m : ℕ), Nat.card K = 2 → 4 ≤ m →
    P 3 (m - 1) (OrthRest.RPlus K m)

@[expose] def GGOrthRestTorusLiftInput : Prop :=
  GGOrthRestAll fun p r R _ => GGTorusLift p r R

@[expose] def GGOrthRestBstarInput : Prop :=
  GGOrthRestAll fun p r R _ => GGBstarBoundInnR p r R (LargeEvenInnSet R)

@[expose] def GGOrthRestEndNodeInput : Prop :=
  GGOrthRestAll fun p r R _ => TableBUR.GGEndNodeEltAdm p r R

@[expose] def GGOrthRestCenterInput : Prop :=
  GGOrthRestAll fun p _ R _ => Subgroup.center R = ⊥ ∧ GGCenterPrime p R

end CFSG.StandardType
