module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSuzukiPrimeSylowLift

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.SuzukiExclusion

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.Blueprint
open CFSG.ShultStronglyClosedTI.ProperPairModel

variable {G : Type} [Group G] [Finite G]

theorem dvd_of_forall_ordProj_dvd {n M : ℕ} (hn : n ≠ 0)
    (h : ∀ p : ℕ, p.Prime → p ∣ n → p ^ n.factorization p ∣ M) : n ∣ M := by
  rcases Nat.eq_zero_or_pos M with hM | hM
  · rw [hM]
    exact dvd_zero n
  rw [← Nat.factorization_le_iff_dvd hn hM.ne']
  intro p
  by_cases hp : p.Prime ∧ p ∣ n
  · exact (hp.1.pow_dvd_iff_le_factorization hM.ne').mp (h p hp.1 hp.2)
  · have : n.factorization p = 0 := by
      by_cases hpp : p.Prime
      · exact Nat.factorization_eq_zero_of_not_dvd fun hd => hp ⟨hpp, hd⟩
      · exact Nat.factorization_eq_zero_of_not_prime n hpp
    rw [this]
    exact Nat.zero_le _

theorem minimalLocalFailure_suzuki_prime_sylow_order_congruence_of_conclusions
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hBinv : ∃ u ∈ pairPointStabilizer H beta, orderOf u = 2)
    (hSz : ∃ (m : ℕ) (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (2 * m + 1) ∧
      Nat.card k = Nat.card (minimalLocalFailurePairActionPointHull H z) ∧
      Nonempty (minimalLocalFailureProperPairHull H z beta t ≃* suzukiGroup m k))
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u) :
    let B := pairPointStabilizer H beta
    let X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta)
    let K := minimalLocalFailureProperPairHull H z beta t
    let Q := minimalLocalFailurePairActionPointHull H z
    let q := Nat.card Q
    let C := H ⊓ Subgroup.centralizer (Q : Set G)
    let J₀ := Subgroup.centralizer (K : Set G)
    ∀ r : ℕ, r.Prime → r ∣ q ^ 2 - q + 1 → ¬ r ∣ Nat.card B → ∀ R : Sylow r ↥H,
      (R : Subgroup ↥H).map H.subtype ≤ C ∧
      Nat.card ((R : Subgroup ↥H).map H.subtype) = r ^ (q ^ 2 - q + 1).factorization r ∧
      Nat.card ((R : Subgroup ↥H).map H.subtype) ≡ 1 [MOD q - 1] ∧
      ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ q - 1 →
        ∃ g ∈ H, ∃ A : Subgroup G, A ≤ J₀ ⊔ X ∧ IsCyclic A ∧
          Nat.card A = ℓ ^ (q - 1).factorization ℓ ∧
          A ≤ Subgroup.normalizer (rightConjugate ((R : Subgroup ↥H).map H.subtype) g : Set G) ∧
          (∀ a ∈ A, a ≠ 1 → Nat.card (rightFixedSet H a) = 2 ∨
            Nat.card (rightFixedSet H a) = q + 1) ∧
          ∀ a ∈ A, a ≠ 1 → rightConjugate ((R : Subgroup ↥H).map H.subtype) g ⊓
            Subgroup.centralizer ({a} : Set G) = ⊥ := by
  intro B X K Q q C J₀ r hr hrN hrB R
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨hHB, -, -, -, -, -, -, -, -, hRC⟩ :=
    minimalLocalFailure_suzuki_scalar_preimage_of_conclusions h hcomm hsmallerR1 hbeta ht hproper
      hBinv hSz hexcl
  obtain ⟨m, -, _, _, -, -, hQcard, -⟩ :=
    proper_pair_suzuki_structure h hcomm hsmallerR1 hbeta ht hproper hSz
  obtain ⟨-, -, hQ4, -⟩ :=
    FixedPointModel.proper_pair_fixed_field_hypotheses h hcomm hsmallerR1 hbeta ht hproper
  have hq4 : 4 ≤ q := hQ4
  have hqeven : Even q := by
    change Even (Nat.card Q)
    rw [hQcard]
    exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact Nat.not_even_iff_odd.mpr (odd_suzuki_norm hqeven) (even_iff_two_dvd.mpr hrN)
  have hBH : B ≤ H := pairPointStabilizer_le_point H beta
  set Rg := (R : Subgroup ↥H).map H.subtype with hRg
  have hRgcard : Nat.card Rg = Nat.card (R : Subgroup H) :=
    Subgroup.card_map_of_injective H.subtype_injective
  have hcardR : Nat.card Rg = r ^ (q ^ 2 - q + 1).factorization r := by
    rw [hRgcard, R.card_eq_multiplicity, card_eq_relIndex_mul_card hBH, hHB]
    have hq0 : q ^ 3 ≠ 0 := pow_ne_zero 3 (by omega)
    have hN0 : q ^ 2 - q + 1 ≠ 0 := by omega
    have hB0 : Nat.card B ≠ 0 := Nat.card_pos.ne'
    rw [Nat.factorization_mul (mul_ne_zero hq0 hN0) hB0, Nat.factorization_mul hq0 hN0]
    simp only [Finsupp.add_apply]
    have hrq : (q ^ 3).factorization r = 0 := by
      refine Nat.factorization_eq_zero_of_not_dvd fun hd => hr2 ?_
      have h2 : r ∣ 2 := by
        change r ∣ Nat.card Q ^ 3 at hd
        rw [hQcard] at hd
        exact hr.dvd_of_dvd_pow (hr.dvd_of_dvd_pow hd)
      exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2
    rw [hrq, Nat.factorization_eq_zero_of_not_dvd hrB, zero_add, add_zero]
  have hlift := fun ℓ (hℓ : ℓ.Prime) (hℓq : ℓ ∣ q - 1) =>
    exists_scalar_lift_of_exclusion h hcomm hsmallerR1 hbeta ht hproper hBinv hSz hexcl hr hrN hrB
      R hℓ hℓq
  have hpart : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ q - 1 → ℓ ^ (q - 1).factorization ℓ ∣ Nat.card Rg - 1 := by
    intro ℓ hℓ hℓq
    obtain ⟨g, -, A, -, -, hAcard, hAN, -, hAC⟩ := hlift ℓ hℓ hℓq
    rw [← hAcard]
    have hRgg : Nat.card (rightConjugate Rg g) = Nat.card Rg :=
      Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
    have hone : (1 : G) ∈ rightConjugate Rg g := Subgroup.one_mem _
    have hdvd := CyclicSemiregular.card_dvd_card_of_free (Ω := G) (fun w a => a⁻¹ * w * a)
      (fun w => by simp) (fun w a b => by simp only [mul_inv_rev]; group) A
      ((rightConjugate Rg g : Set G) \ {1}) (Set.toFinite _)
      (fun w hw a ha => by
        refine ⟨?_, fun h1 => hw.2 ?_⟩
        · have := (Subgroup.mem_normalizer_iff.mp (hAN (A.inv_mem ha)) w).mp hw.1
          rwa [inv_inv] at this
        · rw [Set.mem_singleton_iff] at h1 ⊢
          have h2 := congrArg (fun y => a * y * a⁻¹) h1
          simp only [mul_one, mul_inv_cancel] at h2
          rw [← h2]
          group)
      (fun w hw a ha hwa => by
        by_contra ha1
        have hmem : w ∈ rightConjugate Rg g ⊓ Subgroup.centralizer ({a} : Set G) := by
          refine ⟨hw.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
          calc w * a = a * (a⁻¹ * w * a) := by group
            _ = a * w := by rw [hwa]
        rw [hAC a ha ha1, Subgroup.mem_bot] at hmem
        exact hw.2 hmem)
    rwa [Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem hone, ← Nat.card_coe_set_eq,
      SetLike.coe_sort_coe, hRgg] at hdvd
  have hcong : q - 1 ∣ Nat.card Rg - 1 := dvd_of_forall_ordProj_dvd (by omega) hpart
  refine ⟨hRC r hr hrB R, hcardR, ((Nat.modEq_iff_dvd' Nat.card_pos).mpr hcong).symm,
    fun ℓ hℓ hℓq => hlift ℓ hℓ hℓq⟩

end CFSG.ShultStronglyClosedTI.SuzukiExclusion
