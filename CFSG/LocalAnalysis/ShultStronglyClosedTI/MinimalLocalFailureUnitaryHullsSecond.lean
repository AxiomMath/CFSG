module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureUnitaryHullsCoordinates
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureChainInterface

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.UnitaryHulls

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ShultStronglyClosedTI.FixedPointModel CFSG.ShultStronglyClosedTI.OvergroupHull
open CFSG.ShultStronglyClosedTI.ProperPairModel CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

theorem three_dvd_linear_not_dvd_suzuki {q : ℕ} (hq : (q : ZMod 3) = 2) (h1 : 1 ≤ q) :
    3 ∣ q * (q ^ 2 - 1) ∧ ¬ 3 ∣ q ^ 2 * (q - 1) * (q ^ 2 + 1) := by
  have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  constructor
  · rw [← ZMod.natCast_eq_zero_iff]
    push_cast [Nat.cast_sub h2]
    rw [hq]
    decide
  · rw [← ZMod.natCast_eq_zero_iff]
    push_cast [Nat.cast_sub h1]
    rw [hq]
    decide

theorem cast_two_pow_odd (a : ℕ) : ((2 ^ (2 * a + 1) : ℕ) : ZMod 3) = 2 := by
  rw [Nat.cast_pow, pow_succ, pow_mul]
  have h4 : ((2 : ℕ) : ZMod 3) ^ 2 = 1 := by decide
  rw [h4, one_pow, one_mul]
  rfl

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem baseOrbit_eq_orbit {H L Y : Subgroup G}
    (horbit : {ω : rightCosetSpace H | ∃ y ∈ Y, rightCosetTranslate H (rightCosetMk H 1) y = ω} =
      {ω : rightCosetSpace H | ∃ l ∈ L, rightCosetTranslate H (rightCosetMk H 1) l = ω}) :
    baseOrbit H L =
      {ω : rightCosetSpace H | ∃ y ∈ Y, rightCosetTranslate H (rightCosetMk H 1) y = ω} := by
  rw [horbit]
  ext ω
  simp only [baseOrbit, Set.mem_ofPred_eq, translate_base_mk]

theorem unitary_hull_of_degree
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {Y : Subgroup G} (hY : Y < ⊤) (hKY : minimalLocalFailureProperPairHull H z beta t ≤ Y)
    (hdeg : Nat.card {ω : rightCosetSpace H |
        ∃ y ∈ Y, rightCosetTranslate H (rightCosetMk H 1) y = ω} =
      Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 3 + 1) :
    let q := Nat.card (minimalLocalFailurePairActionPointHull H z)
    let L := Subgroup.closure (involutionPointClass z ∩ (Y : Set G))
    Group.IsPerfect L ∧ IsUnitaryScalarQuotient q L ∧ CFSG.oddCore L ≤ Subgroup.center L ∧
      Nat.card (CFSG.oddCore L) ∣ Nat.gcd 3 (q + 1) ∧ Nat.card (baseOrbit H L) = q ^ 3 + 1 ∧
      minimalLocalFailureProperPairHull H z beta t ≤ L := by
  intro q L
  obtain ⟨-, -, hperfect, hKL, -, hcenter, horbit, -, j, -, -, hΔ, -, -, h3, -⟩ :=
    minimalLocalFailure_proper_overgroup_full_point_hulls h hcomm hsmallerR1 hbeta ht hproper hY
      hKY
  obtain ⟨-, -, -, -, -, hQ4, -⟩ := CyclicPair.proper_pair_point_root h hcomm hbeta ht hproper
  have h' : q ^ j + 1 = q ^ 3 + 1 := hΔ.symm.trans hdeg
  have hj3 : j = 3 := Nat.pow_right_injective (by omega : 2 ≤ q) (by
    change q ^ j = q ^ 3
    omega)
  obtain ⟨k, _, _, J, hJ, hk, hfix, hker, -, C, _, hCker, e, -, hRdvd⟩ := h3 hj3
  refine ⟨hperfect, ⟨k, inferInstance, inferInstance, J, hJ, hk, hfix, C, inferInstance,
    fun A hA => (hker A).mp (hCker hA), ⟨e⟩⟩, hcenter, hRdvd, ?_, hKL⟩
  rw [baseOrbit_eq_orbit horbit]
  exact hdeg

theorem degree_eq_of_linear_of_le
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {Y : Subgroup G} (hY : Y < ⊤) (hKY : minimalLocalFailureProperPairHull H z beta t ≤ Y)
    (hlin : ∃ (k : Type) (_ : Field k) (_ : Finite k),
      Nat.card k = Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
      Nonempty (minimalLocalFailureProperPairHull H z beta t ≃* PSL2MatrixGroup k))
    (hle : Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 2 + 1 ≤
      Nat.card {ω : rightCosetSpace H |
        ∃ y ∈ Y, rightCosetTranslate H (rightCosetMk H 1) y = ω}) :
    Nat.card {ω : rightCosetSpace H |
        ∃ y ∈ Y, rightCosetTranslate H (rightCosetMk H 1) y = ω} =
      Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 3 + 1 := by
  set q := Nat.card (minimalLocalFailurePairActionPointHull H z) with hqdef
  obtain ⟨-, -, -, hKL, -, -, -, -, j, hj123, hjmodel, hΔ, -, h2, -, -⟩ :=
    minimalLocalFailure_proper_overgroup_full_point_hulls h hcomm hsmallerR1 hbeta ht hproper hY
      hKY
  rw [← hqdef] at hjmodel h2
  obtain ⟨-, -, -, -, -, hQ4, -⟩ := CyclicPair.proper_pair_point_root h hcomm hbeta ht hproper
  rw [← hqdef] at hQ4
  obtain ⟨k, _, _, hk, ⟨ψ⟩⟩ := hlin
  rcases hj123 with rfl | rfl | rfl
  · exfalso
    rw [hΔ, pow_one] at hle
    nlinarith
  · exfalso
    obtain ⟨hR, -⟩ := h2 rfl
    rcases hjmodel with ⟨h1, -⟩ | ⟨-, a, -, hqa, -, K', _, _, hK', e, -⟩ | ⟨h1, -⟩
    · omega
    · set L := Subgroup.closure (involutionPointClass z ∩ (Y : Set G))
      have hLcard : Nat.card L = q ^ 2 * (q - 1) * (q ^ 2 + 1) := by
        have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.oddCore L)
        rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK', hR, Subgroup.card_bot,
          mul_one, ← hqa] at hsplit
        exact hsplit
      have hKcard : Nat.card (minimalLocalFailureProperPairHull H z beta t) =
          q * (q ^ 2 - 1) := by
        rw [Nat.card_congr ψ.toEquiv, card_psl2_of_card_two_pow (hk.trans hqa), hk]
      have hdvd := Subgroup.card_dvd_of_le hKL
      rw [hKcard, hLcard] at hdvd
      obtain ⟨h3K, h3L⟩ := three_dvd_linear_not_dvd_suzuki (hqa ▸ cast_two_pow_odd a)
        (by omega)
      exact h3L (dvd_trans h3K hdvd)
    · omega
  · exact hΔ

end CFSG.ShultStronglyClosedTI.UnitaryHulls
