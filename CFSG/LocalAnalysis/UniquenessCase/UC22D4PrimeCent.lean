module

public import CFSG.LocalAnalysis.UniquenessCase.UC22D4PrimeCentRank
import CFSG.LocalAnalysis.UniquenessCase.UC22D4PrimeCentSplit
import CFSG.LocalAnalysis.UniquenessCase.UC22D4PrimeCentQPlus
import CFSG.LocalAnalysis.UniquenessCase.UC22D4PrimeCentThreeSix
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.Chevalley.GraphFixedData

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
open scoped MatrixGroups

theorem uc22d4_prime_dvd_cases {q r : ℕ} (hq : 1 ≤ q) (hr : r.Prime) (h : r ∣ q ^ 6 - 1) :
    r ∣ q - 1 ∨ r ∣ q + 1 ∨ (r : ℤ) ∣ (q : ℤ) ^ 2 + 1 * (q : ℤ) + 1 ∨
      (r : ℤ) ∣ (q : ℤ) ^ 2 + (-1) * (q : ℤ) + 1 := by
  have hq6 : 1 ≤ q ^ 6 := Nat.one_le_pow 6 q (by omega)
  have hcast : ((r : ℕ) : ℤ) ∣ (((q ^ 6 - 1 : ℕ)) : ℤ) := Int.natCast_dvd_natCast.mpr h
  rw [Nat.cast_sub hq6, Nat.cast_pow, Nat.cast_one] at hcast
  have hfac : (q : ℤ) ^ 6 - 1 = ((q : ℤ) - 1) * ((q : ℤ) + 1) *
      ((q : ℤ) ^ 2 + 1 * (q : ℤ) + 1) * ((q : ℤ) ^ 2 + (-1) * (q : ℤ) + 1) := by
    ring
  rw [hfac] at hcast
  rcases Int.Prime.dvd_mul' hr hcast with h12 | h4
  · rcases Int.Prime.dvd_mul' hr h12 with h1 | h3
    · rcases Int.Prime.dvd_mul' hr h1 with h1 | h2
      · left
        exact Int.natCast_dvd_natCast.mp (by rwa [Nat.cast_sub hq])
      · right; left
        exact Int.natCast_dvd_natCast.mp (by rwa [Nat.cast_add, Nat.cast_one])
    · right; right; left
      exact h3
  · right; right; right
    exact h4


theorem uc22d4_centShape {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {r : ℕ} (hr : r.Prime) (hr3 : 3 < r)
    (hrq : r ∣ (ℓ ^ f) ^ 6 - 1) (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hx : orderOf x = r) :
    UC22D4CentShape ℓ (ℓ ^ f)
      (centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) := by
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow f ℓ hℓ.pos
  rcases uc22d4_prime_dvd_cases (q := ℓ ^ f) hq1 hr hrq with h | h | h | h
  · exact uc22d4_centShape_split hℓ hf K hK σ hσ hr hr3 h x hx
  · exact uc22d4_centShape_qplus hℓ hf K hK σ hσ hr hr3 h x hx
  · rcases uc22d4_centShape_threeSix (ε := 1) hℓ hℓ2 hf K hK σ hσ (Or.inl rfl) hr hr3
      (by simpa using h) x hx with ho | hrk
    · exact Or.inr (Or.inl ho)
    · exact Or.inr (Or.inr (Or.inr hrk))
  · rcases uc22d4_centShape_threeSix (ε := -1) hℓ hℓ2 hf K hK σ hσ (Or.inr rfl) hr hr3
      (by simpa using h) x hx with ho | hrk
    · exact Or.inr (Or.inl ho)
    · exact Or.inr (Or.inr (Or.inr hrk))

theorem uc22d4_unique_sl2_or_rank {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ5 : 5 ≤ ℓ) (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {r : ℕ} (hr : r.Prime) (hr3 : 3 < r)
    (hrq : r ∣ (ℓ ^ f) ^ 6 - 1) (x : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hx : orderOf x = r) :
    (∀ L L' : Subgroup (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      L ≤ centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) →
      L' ≤ centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) →
      ∀ (F F' : Type) [Field F] [Field F'] [Finite F] [Finite F'], Nat.card F = ℓ ^ f →
        Nat.card F' = ℓ ^ f → Nonempty (L ≃* SL(2, F)) → Nonempty (L' ≃* SL(2, F')) → L = L') ∨
      2 ≤ CFSG.Open.pRank ℓ
        (centralizer ({x} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))) := by
  have hℓ2 : ℓ ≠ 2 := by omega
  have h4 : 4 ≤ ℓ ^ f := by
    have h1 : ℓ ^ 1 ≤ ℓ ^ f := Nat.pow_le_pow_right hℓ.pos hf
    rw [pow_one] at h1
    omega
  exact uc22d4_unique_sl2_or_rank_of_shape (ℓ := ℓ) (q := ℓ ^ f) h4
    (uc22d4_centShape hℓ hℓ2 hf K hK σ hσ hr hr3 hrq x hx)

end CFSG.LocalAnalysis.UniquenessCase.UC22
