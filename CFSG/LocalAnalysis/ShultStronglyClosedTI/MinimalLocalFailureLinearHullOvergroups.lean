module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPairHullRegularComplement
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePairStabilizerInvolution

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.LinearChain

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.ProperPairModel
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open scoped MatrixGroups

theorem card_psl2_of_card_two_pow {k : Type*} [Field k] [Finite k] {e : ℕ}
    (hk : Nat.card k = 2 ^ e) :
    Nat.card (PSL2MatrixGroup k) = Nat.card k * (Nat.card k ^ 2 - 1) := by
  let : CharP k 2 := LinearModel.charP_two_of_card hk
  have hneg : (-1 : k) = 1 := by
    rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two]
    exact CharP.cast_eq_zero k 2
  have hcard := External.huppert614_card_psl_mul_center (K := k)
  rwa [External.huppert614_card_center_of_neg_one_eq_one hneg, mul_one] at hcard

theorem three_dvd_two_pow_mul (e : ℕ) : 3 ∣ 2 ^ e * ((2 ^ e) ^ 2 - 1) := by
  refine Dvd.dvd.mul_left ?_ _
  have h := Nat.pow_sub_one_dvd_pow_sub_one (x := 2) (dvd_mul_right 2 e)
  rwa [← pow_mul, mul_comm e 2]

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_closure_pointClass_inter (z : G) (Y : Subgroup G) :
    Y ≤ Subgroup.normalizer
      ((Subgroup.closure (involutionPointClass z ∩ (Y : Set G)) : Subgroup G) : Set G) := by
  set L := Subgroup.closure (involutionPointClass z ∩ (Y : Set G))
  have hconj : ∀ g ∈ Y, ∀ x ∈ L, g * x * g⁻¹ ∈ L := by
    intro g hg
    have hle : L ≤ L.comap (MulAut.conj g).toMonoidHom := by
      apply (Subgroup.closure_le _).mpr
      rintro s ⟨hsD, hsY⟩
      apply Subgroup.subset_closure
      change g * s * g⁻¹ ∈ involutionPointClass z ∩ (Y : Set G)
      refine ⟨?_, Y.mul_mem (Y.mul_mem hg hsY) (Y.inv_mem hg)⟩
      simpa only [inv_inv] using PairInvolutionFixedField.conj_mem_pointClass hsD g⁻¹
    exact fun x hx => hle hx
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hconj g hg x, fun hx => ?_⟩
  simpa only [inv_inv, mul_assoc, inv_mul_cancel, mul_one, inv_mul_cancel_left] using
    hconj g⁻¹ (Y.inv_mem hg) _ hx

theorem card_rightCosetSpace_of_conclusions
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hlin : ∃ (k : Type) (_ : Field k) (_ : Finite k),
      Nat.card k = Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
      Nonempty (minimalLocalFailureProperPairHull H z beta t ≃* PSL2MatrixGroup k))
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u) :
    Nat.card (rightCosetSpace H) =
      Nat.card (minimalLocalFailurePairActionPointHull H z) ^ 3 + 1 := by
  obtain ⟨u, huB, hu⟩ := proper_pair_stabilizer_exists_involution h hcomm hbeta ht hproper
  obtain ⟨-, hfixK⟩ :=
    proper_pair_involution_hull_eq_of_conclusions h hcomm hsmallerR1 hbeta ht hproper hexcl huB hu
  obtain ⟨i, -, hfix, hn⟩ := hexcl u huB hu
  obtain ⟨T, -, -, -, -, -, -, -, -, -, -, hTlin, -, -⟩ :=
    minimalLocalFailure_proper_pair_hull_point_normalizer h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨-, hdeg⟩ := hTlin hlin
  obtain ⟨-, hQ4, -⟩ := CyclicPair.proper_pair_cyclic_commutator h hcomm hsmallerR1 hbeta ht hproper
  have h1 : Nat.card (minimalLocalFailurePairActionPointHull H z) ^ i + 1 =
      Nat.card (minimalLocalFailurePairActionPointHull H z) + 1 := by
    rw [← hfix, hfixK]
    exact hdeg
  generalize Nat.card (minimalLocalFailurePairActionPointHull H z) = q at hQ4 h1 hn ⊢
  have hqi : q ^ i = q ^ 1 := by rw [pow_one]; omega
  have hi1 : i = 1 := Nat.pow_right_injective (by omega : 2 ≤ q) hqi
  rw [hn, hi1, pow_one]
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  ring

theorem minimalLocalFailure_linear_hull_proper_overgroups_normalize_of_conclusions
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hlin : ∃ (k : Type) (_ : Field k) (_ : Finite k),
      Nat.card k = Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
      Nonempty (minimalLocalFailureProperPairHull H z beta t ≃* PSL2MatrixGroup k))
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u) :
    let K := minimalLocalFailureProperPairHull H z beta t
    let q := Nat.card (minimalLocalFailurePairActionPointHull H z)
    (∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = q ∧
        Nonempty (K ≃* PSL2MatrixGroup k)) ∧ 4 ≤ q ∧
      Nat.card (rightCosetSpace H) = q ^ 3 + 1 ∧
      ∀ Y : Subgroup G, K ≤ Y → Y < ⊤ →
        Subgroup.closure (involutionPointClass z ∩ (Y : Set G)) = K ∧
          Y ≤ Subgroup.normalizer (K : Set G) := by
  intro K q
  obtain ⟨-, hQ4, hQclass, -⟩ :=
    CyclicPair.proper_pair_cyclic_commutator h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨-, ⟨e, he⟩, -⟩ :=
    FixedPointModel.proper_pair_fixed_field_hypotheses h hcomm hsmallerR1 hbeta ht hproper
  have hq4 : 4 ≤ q := hQ4
  have hn := card_rightCosetSpace_of_conclusions h hcomm hsmallerR1 hbeta ht hproper hlin hexcl
  obtain ⟨k, _, _, hkq, ⟨ψ⟩⟩ := hlin
  refine ⟨⟨k, inferInstance, inferInstance, hkq, ⟨ψ⟩⟩, hq4, hn, fun Y hKY hY => ?_⟩
  obtain ⟨-, -, -, hKL, hQL, -, -, -, j, hj, -, hdegY, hj1, hj2, -, -⟩ :=
    OvergroupHull.minimalLocalFailure_proper_overgroup_full_point_hulls h hcomm hsmallerR1 hbeta
      ht hproper hY hKY
  set L := Subgroup.closure (involutionPointClass z ∩ (Y : Set G)) with hLdef
  have hLY : L ≤ Y := (Subgroup.closure_le _).mpr Set.inter_subset_right
  have hKcard : Nat.card K = q * (q ^ 2 - 1) := by
    rw [Nat.card_congr ψ.toEquiv, card_psl2_of_card_two_pow (hkq.trans he), hkq]
  have hKLeq : K = L := by
    rcases hj with rfl | rfl | rfl
    ·
      obtain ⟨-, f, -, hqf, ⟨eL⟩⟩ := hj1 rfl
      have hqf' : q = 2 ^ f := hqf
      have hf : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by
        rintro rfl
        rw [pow_zero] at hqf'
        omega)
      apply Subgroup.eq_of_le_of_card_ge hKL
      rw [Nat.card_congr eL.toEquiv, card_psl2_of_card_two_pow hf, hf, hKcard, hqf']
    ·
      exfalso
      obtain ⟨-, a, -, hqa, ⟨eL⟩⟩ := hj2 rfl
      have hdvd : Nat.card K ∣ Nat.card L := Subgroup.card_dvd_of_le hKL
      rw [Nat.card_congr eL.toEquiv, card_sz, hKcard] at hdvd
      have hqa' : q = 2 ^ (2 * a + 1) := hqa
      rw [hqa'] at hdvd
      exact three_not_dvd_suzuki_order a ((three_dvd_two_pow_mul _).trans hdvd)
    ·
      exfalso
      have hset : {ω : rightCosetSpace H |
          ∃ y ∈ Y, rightCosetTranslate H (rightCosetMk H 1) y = ω} =
          {ω : rightCosetSpace H | ∃ x ∈ Y, rightCosetMk H x = ω} := by
        ext ω
        simp only [Set.mem_ofPred_eq, rightCosetTranslate_mk, one_mul]
      have hcard : Nat.card (rightCosetSpace H) ≤
          Nat.card {ω : rightCosetSpace H // ∃ x ∈ Y, rightCosetMk H x = ω} := by
        have h1 := hdegY
        rw [hset] at h1
        change Nat.card (rightCosetSpace H) ≤
          Nat.card ↥{ω : rightCosetSpace H | ∃ x ∈ Y, rightCosetMk H x = ω}
        rw [h1, hn]
      have horbit := PairInvolutionsCentralize.orbit_eq_univ_of_card_le hcard
      exact hY.ne (PairInvolutionsCentralize.eq_top_of_orbit_eq_univ h hQclass
        (hQL.trans hLY) horbit)
  refine ⟨hKLeq.symm, ?_⟩
  rw [hKLeq]
  exact le_normalizer_closure_pointClass_inter z Y

end CFSG.ShultStronglyClosedTI.LinearChain
