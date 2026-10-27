module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSuzukiPrimeSylow
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSuzukiPairPrime
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPairHullRegularComplement

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.SuzukiExclusion

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.Blueprint
open CFSG.ShultStronglyClosedTI.ProperPairModel

theorem two_pow_odd_mod_three (m : ℕ) : 2 ^ (2 * m + 1) % 3 = 2 := by
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

theorem suzuki_norm_mod_nine {q : ℕ} (hq : q % 3 = 2) : (q ^ 2 - q + 1) % 9 = 3 := by
  obtain ⟨b, rfl⟩ : ∃ b, q = 3 * b + 2 := ⟨q / 3, by omega⟩
  have h1 : (3 * b + 2) ^ 2 - (3 * b + 2) + 1 = 9 * (b ^ 2 + b) + 3 := by
    have h2 : (3 * b + 2) ^ 2 = 9 * b ^ 2 + 12 * b + 4 := by ring
    rw [h2]
    omega
  rw [h1]
  omega

theorem factorization_eq_one_of_dvd_of_not_sq_dvd {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (h1 : p ∣ n) (h2 : ¬ p ^ 2 ∣ n) : n.factorization p = 1 := by
  have hpos := hp.factorization_pos_of_dvd hn h1
  by_contra hne
  exact h2 ((hp.pow_dvd_iff_le_factorization hn).mpr (by omega))

variable {G : Type} [Group G] [Finite G]

theorem suzuki_branch_false_of_conclusions
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hBinv : ∃ u ∈ pairPointStabilizer H beta, orderOf u = 2)
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u)
    (hSz : ∃ (m : ℕ) (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (2 * m + 1) ∧
      Nat.card k = Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
      Nonempty (minimalLocalFailureProperPairHull H z beta t ≃* suzukiGroup m k)) : False := by
  have hreg := fun u (huB : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2) =>
    proper_pair_hull_regular_complement_of_conclusions h hcomm hsmallerR1 hbeta ht hproper hexcl
      huB hu
  obtain ⟨hpp, -, hcop, -⟩ :=
    SuzukiPairPrime.minimalLocalFailure_suzuki_pair_prime_exception_of_conclusions h hcomm
      hsmallerR1 hbeta ht hproper hBinv hexcl hreg hSz
  have hcong := minimalLocalFailure_suzuki_prime_sylow_order_congruence_of_conclusions h hcomm
    hsmallerR1 hbeta ht hproper hBinv hSz hexcl
  obtain ⟨m, -, _, _, -, -, hQcard, -⟩ :=
    proper_pair_suzuki_structure h hcomm hsmallerR1 hbeta ht hproper hSz
  obtain ⟨-, -, hQ4, -⟩ :=
    FixedPointModel.proper_pair_fixed_field_hypotheses h hcomm hsmallerR1 hbeta ht hproper
  have hq4 : 4 ≤ Nat.card (minimalLocalFailurePairActionPointHull H z) := hQ4
  by_cases hq8 : Nat.card (minimalLocalFailurePairActionPointHull H z) = 8
  ·
    have hN : Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 2 -
        Nat.card (minimalLocalFailurePairActionPointHull H z) + 1 = 57 := by
      rw [hq8]
      norm_num
    have h19 : Nat.Prime 19 := by norm_num
    have h19N : 19 ∣ Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 2 -
        Nat.card (minimalLocalFailurePairActionPointHull H z) + 1 := by
      rw [hN]
      norm_num
    have h19B : ¬ 19 ∣ Nat.card (pairPointStabilizer H beta) := fun h1 => by
      have := (hpp 19 h19 h19N h1).2.1
      norm_num at this
    obtain ⟨-, hcard, hmod, -⟩ := hcong 19 h19 h19N h19B default
    have hv : (Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 2 -
        Nat.card (minimalLocalFailurePairActionPointHull H z) + 1).factorization 19 = 1 := by
      rw [hN]
      exact factorization_eq_one_of_dvd_of_not_sq_dvd h19 (by norm_num) (by norm_num)
        (by norm_num)
    rw [hcard, hv, hq8] at hmod
    exact absurd hmod (by decide)
  ·
    have hq3 : Nat.card (minimalLocalFailurePairActionPointHull H z) % 3 = 2 := by
      rw [hQcard]
      exact two_pow_odd_mod_three m
    have hN9 := suzuki_norm_mod_nine hq3
    have h3 : Nat.Prime 3 := by norm_num
    have h3N : 3 ∣ Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 2 -
        Nat.card (minimalLocalFailurePairActionPointHull H z) + 1 := by omega
    have h3B : ¬ 3 ∣ Nat.card (pairPointStabilizer H beta) := fun h1 => by
      have h2 := Nat.dvd_gcd h1 h3N
      rw [hcop hq8] at h2
      norm_num at h2
    obtain ⟨-, hcard, hmod, -⟩ := hcong 3 h3 h3N h3B default
    have hv : (Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 2 -
        Nat.card (minimalLocalFailurePairActionPointHull H z) + 1).factorization 3 = 1 :=
      factorization_eq_one_of_dvd_of_not_sq_dvd h3 (by omega) h3N (by norm_num; omega)
    rw [hcard, hv, pow_one] at hmod
    have h1 := (Nat.modEq_iff_dvd' (by norm_num : 1 ≤ 3)).mp hmod.symm
    have h2 := Nat.le_of_dvd (by norm_num) h1
    omega

theorem minimalLocalFailure_proper_pair_suzuki_excluded_of_conclusions
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hBinv : ∃ u ∈ pairPointStabilizer H beta, orderOf u = 2)
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u) :
    let K := minimalLocalFailureProperPairHull H z beta t
    let Q := minimalLocalFailurePairActionPointHull H z
    (∃ e : ℕ, 2 ≤ e ∧ Nat.card Q = 2 ^ e ∧ ∃ (k : Type) (_ : Field k) (_ : Finite k),
      Nat.card k = Nat.card Q ∧ Nonempty (K ≃* PSL2MatrixGroup k)) ∧
    (¬ ∃ (m : ℕ) (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (2 * m + 1) ∧
      Nat.card k = Nat.card Q ∧ Nonempty (K ≃* suzukiGroup m k)) ∧
    ¬ ∃ m : ℕ, 1 ≤ m ∧ Nat.card Q = 2 ^ (2 * m + 1) ∧ Nonempty (K ≃* SuzukiMatrixGroup m) := by
  intro K Q
  have hnot : ¬ ∃ (m : ℕ) (k : Type) (_ : Field k) (_ : Finite k),
      Nat.card k = 2 ^ (2 * m + 1) ∧ Nat.card k = Nat.card Q ∧ Nonempty (K ≃* suzukiGroup m k) :=
    fun hSz => suzuki_branch_false_of_conclusions h hcomm hsmallerR1 hbeta ht hproper hBinv hexcl
      hSz
  obtain ⟨-, -, -, hmodel, -⟩ :=
    minimalLocalFailure_proper_pair_hull_linear_or_suzuki h hcomm hsmallerR1 hbeta ht hproper
  have hnot' : ¬ ∃ m : ℕ, 1 ≤ m ∧ Nat.card Q = 2 ^ (2 * m + 1) ∧
      Nonempty (K ≃* SuzukiMatrixGroup m) := by
    rintro ⟨m, -, hQm, ⟨e₀⟩⟩
    have hk : Nat.card (GaloisField 2 (2 * m + 1)) = 2 ^ (2 * m + 1) :=
      GaloisField.card 2 (2 * m + 1) (by omega)
    exact hnot ⟨m, GaloisField 2 (2 * m + 1), inferInstance, inferInstance, hk, hk.trans hQm.symm,
      ⟨e₀.trans (SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hk).symm⟩⟩
  rcases hmodel with ⟨e, he, hQe, -, k, _, _, hk, ψ, -⟩ | ⟨m, -, hQm, -, k, _, _, hk, ψ, -⟩
  · exact ⟨⟨e, he, hQe, k, inferInstance, inferInstance, hk, ⟨ψ⟩⟩, hnot, hnot'⟩
  · exact absurd ⟨m, k, inferInstance, inferInstance, hk, hk.trans hQm.symm, ⟨ψ⟩⟩ hnot

end CFSG.ShultStronglyClosedTI.SuzukiExclusion
