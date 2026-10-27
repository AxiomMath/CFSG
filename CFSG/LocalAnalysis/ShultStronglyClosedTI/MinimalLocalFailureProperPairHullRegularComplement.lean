module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPairHullRegularComplementBasic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureOvergroupHull
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPairPointNormalizer
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPairHullSemiregular

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.ProperPairModel

open CFSG.Open CFSG.BenderSuzuki CFSG.BenderSuzuki.MatrixGroups
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ShultStronglyClosedTI.CyclicPair
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem three_not_dvd_suzuki_order (a : ℕ) :
    ¬ 3 ∣ (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
  have hq : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have hq1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
  have hsq : (2 ^ (2 * a + 1)) ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq]
  intro h3
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h3 | h3
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h3 | h3
    · omega
    · omega
  · omega

theorem three_dvd_two_pow_odd_add_one (a : ℕ) : 3 ∣ 2 ^ (2 * a + 1) + 1 := by
  have hq : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  omega

theorem card_sz (a : ℕ) :
    Nat.card (Sz a) =
      (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) * ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
  have hK : Nat.card (GaloisField 2 (2 * a + 1)) = 2 ^ (2 * a + 1) :=
    GaloisField.card 2 (2 * a + 1) (by omega)
  rw [Nat.card_congr (suzukiCoverNativeEquiv a).toEquiv,
    ← Nat.card_congr (SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK).toEquiv,
    CFSG.LieType.Ree.suzuki_order hK]

theorem proper_pair_involution_hull_eq_of_conclusions
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u)
    {u : G} (huB : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2) :
    Subgroup.closure (involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G)) =
        minimalLocalFailureProperPairHull H z beta t ∧
      rightFixedSet H u = baseOrbit H (minimalLocalFailureProperPairHull H z beta t) := by
  obtain ⟨-, hKu, -⟩ := pairInvolutionCentralizesConclusion h hcomm hsmallerR1 hbeta ht hproper
    u huB hu
  obtain ⟨i', hi', hfix', -⟩ := hexcl u huB hu
  obtain ⟨-, hY, -, -, -, -, hΔ, -⟩ :=
    FixedPointModel.involution_centralizer_fixed_point_model h hcomm hsmallerR1 hbeta ht hproper
      huB hu
  obtain ⟨-, -, -, hKL, -, -, hΔYL, -, j, -, -, hdegY, hj1, hj2, -, -⟩ :=
    OvergroupHull.minimalLocalFailure_proper_overgroup_full_point_hulls h hcomm hsmallerR1 hbeta
      ht hproper hY hKu
  obtain ⟨-, hQ4, -⟩ := proper_pair_cyclic_commutator h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨-, -, -, hmodel, -⟩ :=
    minimalLocalFailure_proper_pair_hull_linear_or_suzuki h hcomm hsmallerR1 hbeta ht hproper
  set K := minimalLocalFailureProperPairHull H z beta t with hKdef
  set Q := minimalLocalFailurePairActionPointHull H z with hQdef
  set L := Subgroup.closure (involutionPointClass z ∩ (Subgroup.centralizer ({u} : Set G) : Set G))
    with hLdef
  have hQ4' : 4 ≤ Nat.card Q := hQ4
  have hfixY : rightFixedSet H u = {ω : rightCosetSpace H |
      ∃ y ∈ Subgroup.centralizer ({u} : Set G), rightCosetTranslate H (rightCosetMk H 1) y = ω} :=
    hΔ
  have hfixL : rightFixedSet H u = {ω : rightCosetSpace H |
      ∃ l ∈ L, rightCosetTranslate H (rightCosetMk H 1) l = ω} := hfixY.trans hΔYL
  have hjeq : j = i' := by
    have h1 : Nat.card Q ^ j + 1 = Nat.card Q ^ i' + 1 := by
      rw [← hdegY, ← hfixY]
      exact hfix'
    exact Nat.pow_right_injective (by omega : 2 ≤ Nat.card Q) (by simpa using h1)
  have hKsub : baseOrbit H K ⊆ rightFixedSet H u := by
    rintro ω ⟨x, hxK, rfl⟩
    rw [hfixL]
    exact ⟨x, hKL hxK, by rw [rightCosetTranslate_mk, one_mul]⟩
  have hcardsub : Nat.card (baseOrbit H K) ≤ Nat.card (rightFixedSet H u) :=
    Nat.card_mono (Set.toFinite _) hKsub
  have hKLeq : K = L := by
    rcases hi' with rfl | rfl
    ·
      obtain ⟨-, f, -, hqf, ⟨eL⟩⟩ := hj1 hjeq
      rcases hmodel with ⟨e, -, hQe, ⟨e₀⟩, -⟩ | ⟨m, -, hQm, -, -, -, -, -, -, -, -, -, -, -, -, -,
        -, hdegK⟩
      · have hef : e = f := Nat.pow_right_injective (le_refl 2) (hQe.symm.trans hqf)
        subst hef
        apply Subgroup.eq_of_le_of_card_ge hKL
        rw [Nat.card_congr eL.toEquiv, Nat.card_congr e₀.toEquiv]
      · exfalso
        have h1 : Nat.card (baseOrbit H K) = Nat.card Q ^ 2 + 1 := hdegK
        rw [h1, hfix'] at hcardsub
        nlinarith
    ·
      obtain ⟨-, a, -, hqa, ⟨eL⟩⟩ := hj2 hjeq
      rcases hmodel with ⟨e, -, hQe, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hdegK⟩ |
        ⟨m, -, hQm, ⟨e₀⟩, -⟩
      · exfalso
        have h1 : Nat.card (baseOrbit H K) = Nat.card Q + 1 := hdegK
        have h3 : 3 ∣ Nat.card K := by
          have hdvd : Nat.card (baseOrbit H K) ∣ Nat.card K :=
            ⟨_, (card_baseOrbit_mul H K).symm⟩
          rw [h1, hqa] at hdvd
          exact (three_dvd_two_pow_odd_add_one a).trans hdvd
        have hKdvd : Nat.card K ∣ Nat.card L := Subgroup.card_dvd_of_le hKL
        rw [Nat.card_congr eL.toEquiv, card_sz] at hKdvd
        exact three_not_dvd_suzuki_order a (h3.trans hKdvd)
      · have hma : m = a :=
          Nat.pow_right_injective (le_refl 2) (by simpa using hQm.symm.trans hqa)
        subst hma
        apply Subgroup.eq_of_le_of_card_ge hKL
        rw [Nat.card_congr eL.toEquiv, Nat.card_congr e₀.toEquiv,
          Nat.card_congr (suzukiCoverNativeEquiv m).toEquiv]
  refine ⟨hKLeq.symm, ?_⟩
  rw [hfixL, ← hKLeq]
  ext ω
  simp only [baseOrbit, Set.mem_ofPred_eq, rightCosetTranslate_mk, one_mul]

theorem proper_pair_hull_regular_complement_of_conclusions
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    (hexcl : ∀ u ∈ pairPointStabilizer H beta, orderOf u = 2 →
      UnitaryFixedModelExcludedConclusion H z u)
    {u : G} (huB : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2) :
    RegularComplementConclusion H z beta t u := by
  obtain ⟨hLu, hfixK⟩ := proper_pair_involution_hull_eq_of_conclusions h hcomm hsmallerR1 hbeta ht
    hproper hexcl huB hu
  obtain ⟨hsimple, -⟩ := minimalLocalFailure_nonabelian_simple h
  obtain ⟨i', hi', hfix', hdeg'⟩ := hexcl u huB hu
  obtain ⟨-, hQ4, -⟩ := proper_pair_cyclic_commutator h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨-, -, -, -, -, -, -, hXcard, -, -⟩ :=
    FixedPointModel.proper_pair_fixed_field_hypotheses h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨-, -, hKB, hmodel, -⟩ :=
    minimalLocalFailure_proper_pair_hull_linear_or_suzuki h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨T, -, -, -, -, hTnormal, hMTX, hTX, -, -, -, hTlin, hTsuz, -⟩ :=
    minimalLocalFailure_proper_pair_hull_point_normalizer h hcomm hsmallerR1 hbeta ht hproper
  set K := minimalLocalFailureProperPairHull H z beta t with hKdef
  set Q := minimalLocalFailurePairActionPointHull H z with hQdef
  set X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta) with hXdef
  set Δ := rightFixedSet H u with hΔdef
  have hQ4' : 4 ≤ Nat.card Q := hQ4
  have hcardM : Nat.card (H ⊓ K : Subgroup G) = Nat.card T * Nat.card X :=
    card_eq_mul_of_semidirect hMTX hTX hTnormal
  have hXc : Nat.card X = Nat.card Q - 1 := hXcard
  have hcardΔK : Nat.card Δ = Nat.card (baseOrbit H K) := by rw [hfixK]
  have hmain : ((∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = Nat.card Q ∧
        Nonempty (K ≃* PSL2MatrixGroup k)) ∧ Nat.card Δ = Nat.card Q + 1 ∨
      (∃ (m : ℕ) (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (2 * m + 1) ∧
        Nat.card k = Nat.card Q ∧ Nonempty (K ≃* CFSG.Blueprint.suzukiGroup m k)) ∧
        Nat.card Δ = Nat.card Q ^ 2 + 1) ∧
      Nat.card K = (Nat.card Q ^ i' + 1) * (Nat.card Q ^ i' * (Nat.card Q - 1)) := by
    rcases hmodel with ⟨e, -, hQe, -, k, hkF, hkfin, hkQ, ψ, -, -, -, f, -, -, -, -, hdegK⟩ |
      ⟨m, -, hQm, -, k, hkF, hkfin, hk, ψ, -, -, -, f, -, -, -, -, hdegK⟩
    · have hdeg1 : Nat.card Δ = Nat.card Q + 1 := hcardΔK.trans hdegK
      have hlin : ∃ (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = Nat.card Q ∧
          Nonempty (K ≃* PSL2MatrixGroup k) := ⟨k, hkF, hkfin, hkQ, ⟨ψ⟩⟩
      have hi1 : i' = 1 := by
        have h1 : Nat.card Q ^ i' = Nat.card Q ^ 1 := by rw [pow_one]; omega
        exact Nat.pow_right_injective (by omega : 2 ≤ Nat.card Q) h1
      subst hi1
      refine ⟨Or.inl ⟨hlin, hdeg1⟩, ?_⟩
      rw [← card_baseOrbit_mul H K, ← hcardΔK, hdeg1, hcardM, (hTlin hlin).1, hXc, pow_one]
    · have hdeg2 : Nat.card Δ = Nat.card Q ^ 2 + 1 := hcardΔK.trans hdegK
      have hsuz : ∃ (m : ℕ) (k : Type) (_ : Field k) (_ : Finite k), Nat.card k = 2 ^ (2 * m + 1) ∧
          Nat.card k = Nat.card Q ∧ Nonempty (K ≃* CFSG.Blueprint.suzukiGroup m k) :=
        ⟨m, k, hkF, hkfin, hk, hk.trans hQm.symm, ⟨ψ⟩⟩
      have hi2 : i' = 2 := by
        have h1 : Nat.card Q ^ i' = Nat.card Q ^ 2 := by omega
        exact Nat.pow_right_injective (by omega : 2 ≤ Nat.card Q) h1
      subst hi2
      refine ⟨Or.inr ⟨hsuz, hdeg2⟩, ?_⟩
      rw [← card_baseOrbit_mul H K, ← hcardΔK, hdeg2, hcardM, (hTsuz hsuz).1, hXc]
  obtain ⟨hmodelΔ, hcardK⟩ := hmain
  have hΓcard : Nat.card ↥Δᶜ = Nat.card K := by
    have h1 := Set.ncard_add_ncard_compl Δ
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq] at h1
    rw [hcardK]
    have h2 : Nat.card Δ = Nat.card Q ^ i' + 1 := hfix'
    rw [h2, hdeg'] at h1
    have h3 : (Nat.card Q ^ i' + 1) * (Nat.card Q ^ i' * (Nat.card Q - 1) + 1) =
        (Nat.card Q ^ i' + 1) + (Nat.card Q ^ i' + 1) * (Nat.card Q ^ i' * (Nat.card Q - 1)) := by
      ring
    omega
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hΓne : (Δᶜ).Nonempty := by
    have h1 : 0 < Nat.card ↥Δᶜ := hΓcard ▸ hKpos
    obtain ⟨⟨γ, hγ⟩⟩ := Nat.card_pos_iff.mp h1 |>.1
    exact ⟨γ, hγ⟩
  have hΔinv : ∀ ω ∈ Δ, ∀ x ∈ K, rightCosetTranslate H ω x ∈ Δ := by
    intro ω hω x hx
    rw [hfixK] at hω ⊢
    obtain ⟨y, hyK, rfl⟩ := hω
    exact ⟨y * x, K.mul_mem hyK hx, by rw [rightCosetTranslate_mk]⟩
  have hΓinv : ∀ ω ∈ Δᶜ, ∀ x ∈ K, rightCosetTranslate H ω x ∈ Δᶜ := by
    intro ω hω x hx hωx
    apply hω
    have h1 := hΔinv _ hωx x⁻¹ (K.inv_mem hx)
    rwa [rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one] at h1
  have hsemi : ∀ ω ∈ Δᶜ, ∀ x : K, rightCosetTranslate H ω x = ω → x = 1 := by
    intro ω hω x hx
    by_contra hx1
    have hx1' : (x : G) ≠ 1 := fun h1 => hx1 (Subtype.ext h1)
    obtain ⟨k, hkK, hk⟩ := proper_pair_hull_fixed_points_in_orbit h hcomm hsmallerR1 hbeta ht
      hproper x.2 hx1' hx
    apply hω
    rw [hfixK]
    exact ⟨k, hkK, hk⟩
  have hregΓ : ∀ ω ∈ Δᶜ, ∀ ω' ∈ Δᶜ, ∃! x : K, rightCosetTranslate H ω x = ω' := by
    intro ω hω
    let φ : K → ↥Δᶜ := fun x => ⟨rightCosetTranslate H ω x, hΓinv ω hω x x.2⟩
    have hφinj : Function.Injective φ := by
      intro x y hxy
      have h1 : rightCosetTranslate H ω x = rightCosetTranslate H ω y := congrArg Subtype.val hxy
      have h2 : rightCosetTranslate H ω ((x * y⁻¹ : K) : G) = ω := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, ← rightCosetTranslate_mul, h1,
          rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one]
      have h3 := hsemi ω hω _ h2
      exact mul_inv_eq_one.mp h3
    have hφbij : Function.Bijective φ :=
      (Function.Injective.bijective_of_nat_card_le hφinj (le_of_eq hΓcard))
    intro ω' hω'
    obtain ⟨x, hx⟩ := hφbij.2 ⟨ω', hω'⟩
    refine ⟨x, congrArg Subtype.val hx, fun y hy => hφinj (Subtype.ext ?_)⟩
    exact hy.trans (congrArg Subtype.val hx).symm
  have hzK : z ∈ K := minimalLocalFailureProperPair_distinguished_mem H z beta t
  have hzfix := ((involution_point_unique_containment_action h.local_datum.distinguished_mem
    h.local_datum.distinguished_order).2 h.local_datum.unique_containment).2.2.1
  have hCα : ∀ c ∈ Subgroup.centralizer (K : Set G),
      rightCosetTranslate H (rightCosetMk H 1) c = rightCosetMk H 1 := by
    intro c hc
    have hcz : c * z = z * c := (Subgroup.mem_centralizer_iff.mp hc z hzK).symm
    apply (hzfix _).mp
    rw [pointRightCosetMul_eq_translate,
      rightCosetTranslate_mul, hcz, ← rightCosetTranslate_mul]
    have h1 : rightCosetTranslate H (rightCosetMk H 1) z = rightCosetMk H 1 := by
      rw [← pointRightCosetMul_eq_translate]
      exact (hzfix _).mpr rfl
    rw [h1]
  have hCΔ : ∀ c ∈ Subgroup.centralizer (K : Set G), ∀ ω ∈ Δ, rightCosetTranslate H ω c = ω := by
    intro c hc ω hω
    rw [hfixK] at hω
    obtain ⟨x, hxK, rfl⟩ := hω
    have hxc : c * x = x * c := (Subgroup.mem_centralizer_iff.mp hc x hxK).symm
    calc rightCosetTranslate H (rightCosetMk H x) c
        = rightCosetTranslate H (rightCosetTranslate H (rightCosetMk H 1) c) x := by
          rw [rightCosetTranslate_mul, rightCosetTranslate_mk, rightCosetTranslate_mk, one_mul,
            hxc]
      _ = rightCosetMk H x := by rw [hCα c hc, rightCosetTranslate_mk, one_mul]
  have hCfaith : ∀ c ∈ Subgroup.centralizer (K : Set G),
      (∀ ω ∈ Δᶜ, rightCosetTranslate H ω c = ω) → c = 1 := by
    intro c hc hΓfix
    apply MixedClass.eq_one_of_fixes_all hsimple h.local_datum.proper
    intro ω
    by_cases hω : ω ∈ Δ
    · exact hCΔ c hc ω hω
    · exact hΓfix ω hω
  have hCΓ : ∀ c ∈ Subgroup.centralizer (K : Set G), ∀ ω ∈ Δᶜ,
      rightCosetTranslate H ω c ∈ Δᶜ := by
    intro c hc ω hω hωc
    apply hω
    have h1 := hCΔ c⁻¹ (Subgroup.inv_mem _ hc) _ hωc
    rw [rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one] at h1
    rw [h1]
    exact hωc
  have hCK : ∀ c ∈ Subgroup.centralizer (K : Set G), ∀ x ∈ K, c * x = x * c :=
    fun c hc x hx => (Subgroup.mem_centralizer_iff.mp hc x hx).symm
  obtain ⟨φ, hφ⟩ := exists_injective_hom_of_regular H K (Subgroup.centralizer (K : Set G)) Δᶜ
    hΓne hregΓ hCK hCΓ hCfaith
  exact ⟨hLu, hfixK, hmodelΔ, hΓne, hΓinv, hΓcard, hregΓ, hCΔ, hCfaith, φ, hφ⟩

end CFSG.ShultStronglyClosedTI.ProperPairModel
