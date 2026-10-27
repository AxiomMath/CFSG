module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureAmbientDegree
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCyclicSemiregular
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPairLinearOrSuzuki
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDegreeArithmetic

public section

namespace CFSG.ShultStronglyClosedTI.PairInvolutionsCentralize

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ShultStronglyClosedTI
open CFSG.ShultStronglyClosedTI.MixedClass
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionDegreeArithmetic
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type} [Group G] [Finite G]

theorem eq_top_of_orbit_eq_univ {H Q K : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z)
    (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z) (hQK : Q ≤ K)
    (horbit : ∀ ω : rightCosetSpace H, ∃ x ∈ K, rightCosetMk H x = ω) : K = ⊤ := by
  have hD : involutionPointClass z ⊆ K := by
    intro r hr
    obtain ⟨γ, hγ⟩ := class_fixed_exists h.local_datum hr
    obtain ⟨x, hxK, rfl⟩ := horbit γ
    have hrQ := conj_mem_point_subgroup_of_fixed h.local_datum hQclass hr hγ
    have hmem := K.mul_mem (K.mul_mem (K.inv_mem hxK) (hQK hrQ)) hxK
    rwa [show x⁻¹ * (x * r * x⁻¹) * x = r by group] at hmem
  have hle : involutionPointHull z ≤ K := (Subgroup.closure_le _).mpr hD
  rw [minimalLocalFailure_hull_eq_top h] at hle
  exact top_unique hle

theorem orbit_eq_univ_of_card_le {H K : Subgroup G}
    (hcard : Nat.card (rightCosetSpace H) ≤
      Nat.card {ω : rightCosetSpace H // ∃ x ∈ K, rightCosetMk H x = ω}) :
    ∀ ω : rightCosetSpace H, ∃ x ∈ K, rightCosetMk H x = ω := by
  have huniv : {ω : rightCosetSpace H | ∃ x ∈ K, rightCosetMk H x = ω} = Set.univ := by
    refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_
    rw [Set.ncard_univ, ← Nat.card_coe_set_eq]
    exact hcard
  intro ω
  have hω : ω ∈ {ω : rightCosetSpace H | ∃ x ∈ K, rightCosetMk H x = ω} :=
    huniv ▸ Set.mem_univ ω
  exact hω

theorem card_rightCosetSpace_ne_succ
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    Nat.card (rightCosetSpace H) ≠ Nat.card (minimalLocalFailurePairActionPointHull H z) + 1 := by
  intro hn
  obtain ⟨-, -, hQclass, -⟩ :=
    CyclicPair.proper_pair_cyclic_commutator h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨-, hQK, -⟩ := CyclicPair.proper_pair_point_root h hcomm hbeta ht hproper
  obtain ⟨-, -, -, hmodel, -⟩ :=
    ProperPairModel.minimalLocalFailure_proper_pair_hull_linear_or_suzuki h hcomm hsmallerR1
      hbeta ht hproper
  have horbcard : Nat.card (minimalLocalFailurePairActionPointHull H z) + 1 ≤
      Nat.card {ω : rightCosetSpace H //
        ∃ x ∈ minimalLocalFailureProperPairHull H z beta t, rightCosetMk H x = ω} := by
    rcases hmodel with
      ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcard⟩ |
      ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcard⟩
    · exact hcard.ge
    · rw [hcard]
      have h1 : Nat.card (minimalLocalFailurePairActionPointHull H z) ≤
          Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 2 :=
        Nat.le_self_pow (by norm_num) _
      omega
  have horbit := orbit_eq_univ_of_card_le (hn ▸ horbcard)
  exact hproper.ne (eq_top_of_orbit_eq_univ h hQclass hQK horbit)


theorem pair_involution_centralizes_point_group
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {u : G} (huB : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2) :
    minimalLocalFailurePairActionPointHull H z ≤ Subgroup.centralizer ({u} : Set G) := by
  by_contra hQu
  obtain ⟨hq₀4, i, hi, -, -, -, -, hnon⟩ :=
    AmbientDegree.minimalLocalFailure_pair_involution_ambient_degree_formulas h hcomm hsmallerR1
      hbeta ht hproper huB hu
  obtain ⟨hsq, -, hn⟩ := hnon hQu
  obtain ⟨-, -, hQclass, -⟩ :=
    CyclicPair.proper_pair_cyclic_commutator h hcomm hsmallerR1 hbeta ht hproper
  set q₀ := Nat.card (minimalLocalFailurePairActionPointHull H z ⊓
    Subgroup.centralizer ({u} : Set G) : Subgroup G) with hq₀def
  have hcast : ((q₀ - 1 : ℕ) : ℚ) = (q₀ : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hnR : (Nat.card (rightCosetSpace H) : ℚ) * ((q₀ : ℚ) + 1) =
      ((q₀ : ℚ) ^ i + 1) * ((q₀ : ℚ) ^ i * ((q₀ : ℚ) - 1) + q₀ + 1) := by
    rw [← hcast]
    exact_mod_cast hn
  have hnQ : (Nat.card (rightCosetSpace H) : ℚ) = degreeG i (q₀ : ℤ) := by
    unfold degreeG
    rw [Int.cast_natCast, eq_div_iff (by positivity)]
    exact hnR
  obtain ⟨harith, -⟩ := fixed_parameter_involution_degree_arithmetic
  obtain ⟨-, -, -, -, -, hG1, -, hG2, hG3⟩ := harith (q₀ : ℤ) (by exact_mod_cast hq₀4)
  rcases hi with rfl | rfl | rfl
  ·
    have hn1 : Nat.card (rightCosetSpace H) =
        Nat.card (minimalLocalFailurePairActionPointHull H z) + 1 := by
      rw [hsq]
      have hq := hnQ.trans hG1
      rw [Int.cast_natCast] at hq
      exact_mod_cast hq
    exact card_rightCosetSpace_ne_succ h hcomm hsmallerR1 hbeta ht hproper hn1
  · exact hG2 ⟨Nat.card (rightCosetSpace H), by rw [← hnQ, Int.cast_natCast]⟩
  ·
    obtain ⟨-, -, -, -, -, -, hdvd⟩ :=
      CyclicSemiregular.minimalLocalFailure_proper_pair_cyclic_semiregularity h hcomm
        hsmallerR1 hbeta ht hproper
    apply hG3 (Nat.card (rightCosetSpace H)) (by rw [← hnQ, Int.cast_natCast])
    have hm : Nat.card (conjugacyWithin H z) = q₀ ^ 2 - 1 := by
      rw [← hQclass, card_diff_one, hsq]
    have hn2 : 2 ≤ Nat.card (rightCosetSpace H) :=
      Finite.one_lt_card_iff_nontrivial.mpr (nontrivial_of_ne _ _ hbeta)
    have hq1 : 1 ≤ q₀ ^ 2 := Nat.one_le_pow _ _ (by omega)
    have hdvd' : ((q₀ ^ 2 - 1 : ℕ) : ℤ) ∣ ((Nat.card (rightCosetSpace H) - 2 : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.mpr (hm ▸ hdvd)
    rw [Nat.cast_sub hq1, Nat.cast_sub hn2] at hdvd'
    push_cast at hdvd'
    exact hdvd'

theorem minimalLocalFailure_pair_involutions_centralize_point_group
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤) :
    let B := pairPointStabilizer H beta
    let K := minimalLocalFailureProperPairHull H z beta t
    let Q := minimalLocalFailurePairActionPointHull H z
    let q := Nat.card Q
    let n := Nat.card (rightCosetSpace H)
    ∀ u ∈ B, orderOf u = 2 →
      Q ≤ Subgroup.centralizer ({u} : Set G) ∧ K ≤ Subgroup.centralizer ({u} : Set G) ∧
        ∃ i : ℕ, (i = 1 ∨ i = 2 ∨ i = 3) ∧
          Nat.card {omega : rightCosetSpace H | rightCosetTranslate H omega u = omega} =
            q ^ i + 1 ∧
          n = (q ^ i + 1) * (q ^ i * (q - 1) + 1) := by
  intro B K Q q n u huB hu
  have hQu : Q ≤ Subgroup.centralizer ({u} : Set G) :=
    pair_involution_centralizes_point_group h hcomm hsmallerR1 hbeta ht hproper huB hu
  obtain ⟨-, -, -, -, -, -, hclauses⟩ :=
    ProperPairModel.minimalLocalFailure_proper_pair_hull_linear_or_suzuki h hcomm hsmallerR1
      hbeta ht hproper
  have hKu : K ≤ Subgroup.centralizer ({u} : Set G) := (hclauses u huB hu).2.1 hQu
  obtain ⟨-, i, hi, hd, -, -, hcen, -⟩ :=
    AmbientDegree.minimalLocalFailure_pair_involution_ambient_degree_formulas h hcomm hsmallerR1
      hbeta ht hproper huB hu
  obtain ⟨hQq, -, hn⟩ := hcen hQu
  have hq : q = Nat.card (Q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) := hQq
  refine ⟨hQu, hKu, i, hi, ?_, ?_⟩
  · rw [hq]
    exact hd
  · rw [hq]
    exact hn

end CFSG.ShultStronglyClosedTI.PairInvolutionsCentralize
