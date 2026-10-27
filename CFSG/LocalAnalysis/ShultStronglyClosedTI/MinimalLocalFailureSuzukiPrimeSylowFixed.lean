module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RegularOrbitProductCount
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPairHullRegularComplement
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureChainInterface
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCyclicSemiregular
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPairLinearOrSuzuki

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.SuzukiExclusion

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.Blueprint
open CFSG.ShultStronglyClosedTI.ProperPairModel

variable {G : Type} [Group G] [Finite G]

theorem hull_inf_centralizer_torus_eq
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {x : G} (hx : x ∈ rightInvolutionCommutatorSubgroup t (pairOddCore H beta)) (hx1 : x ≠ 1) :
    minimalLocalFailureProperPairHull H z beta t ⊓ Subgroup.centralizer ({x} : Set G) =
      rightInvolutionCommutatorSubgroup t (pairOddCore H beta) := by
  set X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta) with hXdef
  set K := minimalLocalFailureProperPairHull H z beta t with hKdef
  obtain ⟨-, -, hKB, -⟩ :=
    minimalLocalFailure_proper_pair_hull_linear_or_suzuki h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨-, -, -, -, -, -, -, -, -, hXK, hXcyc, hXodd, -, -, -, hXinv, -, -⟩ :=
    CyclicPair.proper_pair_cyclic_commutator h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨-, -, -, -, -, hfix, -⟩ :=
    CyclicSemiregular.minimalLocalFailure_proper_pair_cyclic_semiregularity h hcomm hsmallerR1
      hbeta ht hproper
  have hKB' : K ⊓ pairPointStabilizer H beta = X := hKB
  have hXK' : X ≤ K := hXK
  have htK : t ∈ K := minimalLocalFailureProperPair_flip_mem H z beta t
  have ht2 : t * t = 1 := by
    have := order_two_of_mem_pointClass h.local_datum.distinguished_order ht.1
    rw [← sq, ← this, pow_orderOf_eq_one]
  have htα : rightCosetTranslate H (rightCosetMk H 1) t = beta := ht.2
  have htβ : rightCosetTranslate H beta t = rightCosetMk H 1 := by
    rw [← htα, rightCosetTranslate_mul, ht2, rightCosetTranslate_one]
  have hfixx := hfix x hx hx1
  have hmemfix : ∀ ω, rightCosetTranslate H ω x = ω ↔ ω = rightCosetMk H 1 ∨ ω = beta :=
    fun ω => by
      have : ω ∈ {ω : rightCosetSpace H | rightCosetTranslate H ω x = ω} ↔
          ω ∈ ({rightCosetMk H 1, beta} : Set (rightCosetSpace H)) := by rw [hfixx]
      simpa using this
  have hXab : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := fun a ha b hb => by
    have := hXcyc.commGroup.mul_comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this
  refine le_antisymm (fun c hc => ?_) (fun y hy => ⟨hXK' hy,
    Subgroup.mem_centralizer_singleton_iff.mpr (hXab y hy x hx)⟩)
  obtain ⟨hcK, hcx⟩ := hc
  have hcx' := Subgroup.mem_centralizer_singleton_iff.mp hcx
  have hpres : ∀ ω, rightCosetTranslate H ω x = ω →
      rightCosetTranslate H (rightCosetTranslate H ω c) x = rightCosetTranslate H ω c := by
    intro ω hω
    rw [rightCosetTranslate_mul, hcx', ← rightCosetTranslate_mul, hω]
  have hinj : ∀ ω ω', rightCosetTranslate H ω c = rightCosetTranslate H ω' c → ω = ω' := by
    intro ω ω' h1
    have h2 := congrArg (fun w => rightCosetTranslate H w c⁻¹) h1
    simpa only [rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one] using h2
  have hα := (hmemfix _).mp (hpres _ ((hmemfix _).mpr (Or.inl rfl)))
  have hβ := (hmemfix _).mp (hpres _ ((hmemfix _).mpr (Or.inr rfl)))
  have hKBX : ∀ w ∈ K, rightCosetTranslate H (rightCosetMk H 1) w = rightCosetMk H 1 →
      rightCosetTranslate H beta w = beta → w ∈ X := fun w hw h1 h2 => by
    rw [← hKB']
    exact ⟨hw, (mem_rightCosetStabilizer_iff H _ w).mpr h1,
      (mem_rightCosetStabilizer_iff H _ w).mpr h2⟩
  rcases hα with hα | hα
  ·
    rcases hβ with hβ | hβ
    · exact absurd (hinj _ _ (hβ.trans hα.symm)) hbeta
    · exact hKBX c hcK hα hβ
  ·
    rcases hβ with hβ | hβ
    · have hct : c * t ∈ X := hKBX (c * t) (K.mul_mem hcK htK)
        (by rw [← rightCosetTranslate_mul, hα, htβ])
        (by rw [← rightCosetTranslate_mul, hβ, htα])
      exfalso
      have hcinv : c * x * c⁻¹ = x⁻¹ := by
        have h1 : t⁻¹ * x * t = x⁻¹ := hXinv x hx
        calc c * x * c⁻¹ = (c * t) * (t⁻¹ * x * t) * (c * t)⁻¹ := by group
          _ = x⁻¹ := by rw [h1, hXab _ hct _ (X.inv_mem hx), mul_inv_cancel_right]
      have hxx : x = x⁻¹ := by
        rw [← hcinv, hcx', mul_inv_cancel_right]
      have hx2 : x ^ 2 = 1 := by rw [sq]; nth_rewrite 2 [hxx]; exact mul_inv_cancel x
      have hdvd := orderOf_dvd_of_pow_eq_one hx2
      have hodd := hXodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard X hx)
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
      · exact hx1 (orderOf_eq_one_iff.mp h1)
      · rw [h1] at hodd
        exact absurd hodd (by decide)
    · exact absurd (hinj _ _ (hα.trans hβ.symm)) (Ne.symm hbeta)

theorem card_fixed_mul_torus_of_exclusion
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
    {j x : G} (hj : j ∈ Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G))
    (hx : x ∈ rightInvolutionCommutatorSubgroup t (pairOddCore H beta)) (hx1 : x ≠ 1) :
    Nat.card (rightFixedSet H (j * x)) = 2 ∨
      Nat.card (rightFixedSet H (j * x)) =
        Nat.card (minimalLocalFailurePairActionPointHull H z) + 1 := by
  obtain ⟨u, huB, hu⟩ := hBinv
  obtain ⟨-, hfixu, -, -, hΓinv, -, hregΓ, hJΔ, -, -⟩ :=
    proper_pair_hull_regular_complement_of_conclusions h hcomm hsmallerR1 hbeta ht hproper hexcl
      huB hu
  obtain ⟨-, -, -, -, -, -, -, -, -, hXK, -⟩ :=
    CyclicPair.proper_pair_cyclic_commutator h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨-, -, -, -, hXB, -, -, hXcard, -, -⟩ :=
    FixedPointModel.proper_pair_fixed_field_hypotheses h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨-, -, -, -, -, hfix, -⟩ :=
    CyclicSemiregular.minimalLocalFailure_proper_pair_cyclic_semiregularity h hcomm hsmallerR1
      hbeta ht hproper
  have hcount := MiscAlgebra.commuting_regular_orbit_product_fixed_point_count
    (rightCosetTranslate H) (rightCosetTranslate_one H) (rightCosetTranslate_mul H)
    (K := minimalLocalFailureProperPairHull H z beta t)
    (J := Subgroup.centralizer (minimalLocalFailureProperPairHull H z beta t : Set G))
    (Δ := rightFixedSet H u) (Γ := (rightFixedSet H u)ᶜ) isCompl_compl
    (fun k hk γ hγ => hΓinv γ hγ k hk)
    (fun γ hγ γ' hγ' => by
      obtain ⟨⟨k, hk⟩, hk', -⟩ := hregΓ γ hγ γ' hγ'
      exact ⟨k, hk, hk'⟩)
    (fun γ hγ k hk hkγ => by
      obtain ⟨w, -, hw⟩ := hregΓ γ hγ γ hγ
      have h1 := hw ⟨k, hk⟩ hkγ
      have h2 := hw 1 (rightCosetTranslate_one H γ)
      exact congrArg Subtype.val (h1.trans h2.symm))
    le_rfl hJΔ (hXK hx) hj
  obtain ⟨-, hor, -⟩ := hcount
  have hΔx : {δ | δ ∈ rightFixedSet H u ∧ rightCosetTranslate H δ x = δ} =
      ({rightCosetMk H 1, beta} : Set (rightCosetSpace H)) := by
    rw [← hfix x hx hx1]
    ext δ
    refine ⟨fun hδ => hδ.2, fun hδ => ⟨?_, hδ⟩⟩
    have hδ' : δ ∈ ({rightCosetMk H 1, beta} : Set (rightCosetSpace H)) := by
      rw [← hfix x hx hx1]; exact hδ
    rw [hfixu]
    rcases hδ' with rfl | hδ'
    · exact ⟨1, Subgroup.one_mem _, rfl⟩
    · rw [Set.mem_singleton_iff] at hδ'
      rw [hδ']
      exact ⟨t, minimalLocalFailureProperPair_flip_mem H z beta t, (flip_coset_eq H ht).symm⟩
  have hcard2 : Nat.card {δ | δ ∈ rightFixedSet H u ∧ rightCosetTranslate H δ x = δ} = 2 := by
    rw [hΔx, Nat.card_coe_set_eq, Set.ncard_pair hbeta.symm]
  have hCK : Nat.card (minimalLocalFailureProperPairHull H z beta t ⊓
      Subgroup.centralizer ({x} : Set G) : Subgroup G) =
        Nat.card (minimalLocalFailurePairActionPointHull H z) - 1 := by
    rw [hull_inf_centralizer_torus_eq h hcomm hsmallerR1 hbeta ht hproper hx hx1, hXcard]
  have hq : 1 ≤ Nat.card (minimalLocalFailurePairActionPointHull H z) := Nat.card_pos
  rcases hor with h1 | h1
  · left
    rw [← hcard2]
    exact h1
  · right
    change Nat.card {ω | rightCosetTranslate H ω (j * x) = ω} = _
    rw [h1, hcard2, hCK]
    omega

omit [Finite G] in
theorem orderOf_dvd_card_pair_stabilizer [Finite G] {H : Subgroup G} {beta : rightCosetSpace H}
    (hbeta : beta ≠ rightCosetMk H 1)
    (htwo : ∀ a b c d : rightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, rightCosetTranslate H a g = c ∧ rightCosetTranslate H b g = d)
    {y : G} (hyH : y ∈ H) {ω : rightCosetSpace H} (hω : ω ≠ rightCosetMk H 1)
    (hyω : rightCosetTranslate H ω y = ω) :
    orderOf y ∣ Nat.card (pairPointStabilizer H beta) := by
  obtain ⟨g, hgα, hgβ⟩ := htwo (rightCosetMk H 1) beta (rightCosetMk H 1) ω hbeta.symm
    (Ne.symm hω)
  have hgα' : rightCosetTranslate H (rightCosetMk H 1) g⁻¹ = rightCosetMk H 1 := by
    rw [← hgα, rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one, hgα]
  have hgβ' : rightCosetTranslate H ω g⁻¹ = beta := by
    rw [← hgβ, rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one]
  have hyα : rightCosetTranslate H (rightCosetMk H 1) y = rightCosetMk H 1 :=
    (PairInvolutionFixedField.translate_base_iff H y).mpr hyH
  have hmem : g * y * g⁻¹ ∈ pairPointStabilizer H beta := by
    refine ⟨(mem_rightCosetStabilizer_iff H _ _).mpr ?_,
      (mem_rightCosetStabilizer_iff H _ _).mpr ?_⟩
    · rw [← rightCosetTranslate_mul, ← rightCosetTranslate_mul, hgα, hyα, hgα']
    · rw [← rightCosetTranslate_mul, ← rightCosetTranslate_mul, hgβ, hyω, hgβ']
  have h1 := Subgroup.orderOf_dvd_natCard _ hmem
  rwa [← MulAut.conj_apply, MulEquiv.orderOf_eq] at h1

omit [Finite G] in
theorem inf_centralizer_eq_bot_of_card_fixed [Finite G] {H : Subgroup G}
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    (htwo : ∀ a b c d : rightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, rightCosetTranslate H a g = c ∧ rightCosetTranslate H b g = d)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrB : ¬ r ∣ Nat.card (pairPointStabilizer H beta))
    {R₁ : Subgroup G} (hR₁H : R₁ ≤ H) (hR₁ : IsPGroup r R₁) {a : G} (haH : a ∈ H) {n : ℕ}
    (hfixa : Nat.card (rightFixedSet H a) = 2 ∨ Nat.card (rightFixedSet H a) = 2 ^ n + 1) :
    R₁ ⊓ Subgroup.centralizer ({a} : Set G) = ⊥ := by
  have : Fact r.Prime := ⟨hr⟩
  set L := R₁ ⊓ Subgroup.centralizer ({a} : Set G) with hL
  set Γ := rightFixedSet H a \ {rightCosetMk H 1} with hΓ
  have hαa : rightCosetMk H 1 ∈ rightFixedSet H a :=
    (PairInvolutionFixedField.translate_base_iff H a).mpr haH
  have hpres : ∀ ω ∈ Γ, ∀ y ∈ L, rightCosetTranslate H ω y ∈ Γ := by
    rintro ω ⟨hωa, hωα⟩ y ⟨hyR, hya⟩
    have hya' := Subgroup.mem_centralizer_singleton_iff.mp hya
    refine ⟨?_, fun h1 => hωα ?_⟩
    · change rightCosetTranslate H (rightCosetTranslate H ω y) a = rightCosetTranslate H ω y
      rw [rightCosetTranslate_mul, hya', ← rightCosetTranslate_mul, hωa]
    · rw [Set.mem_singleton_iff] at h1 ⊢
      have h2 := congrArg (fun w => rightCosetTranslate H w y⁻¹) h1
      simp only [rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one] at h2
      rw [h2]
      exact (PairInvolutionFixedField.translate_base_iff H y⁻¹).mpr (H.inv_mem (hR₁H hyR))
  have hfree : ∀ ω ∈ Γ, ∀ y ∈ L, rightCosetTranslate H ω y = ω → y = 1 := by
    rintro ω ⟨-, hωα⟩ y ⟨hyR, -⟩ hyω
    by_contra hy1
    have h1 := orderOf_dvd_card_pair_stabilizer hbeta htwo (hR₁H hyR) hωα hyω
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hR₁) ⟨y, hyR⟩
    rw [Subgroup.orderOf_mk] at hk
    rcases k with _ | k
    · rw [pow_zero, orderOf_eq_one_iff] at hk
      exact hy1 hk
    · rw [hk] at h1
      exact hrB ((dvd_pow_self r k.succ_ne_zero).trans h1)
  have hdvd := CyclicSemiregular.card_dvd_card_of_free (rightCosetTranslate H)
    (rightCosetTranslate_one H) (rightCosetTranslate_mul H) L Γ (Set.toFinite _) hpres hfree
  have hΓcard : Nat.card Γ = Nat.card (rightFixedSet H a) - 1 := by
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, hΓ, Set.ncard_sdiff_singleton_of_mem hαa]
  obtain ⟨k, hk⟩ := (hR₁.to_le inf_le_left : IsPGroup r L).exists_card_eq
  rw [hΓcard, hk] at hdvd
  have hrk : r ^ k = 1 := by
    rcases hfixa with h1 | h1
    · rw [h1] at hdvd
      exact Nat.dvd_one.mp hdvd
    · rw [h1, Nat.add_sub_cancel] at hdvd
      have hcop : Nat.Coprime (r ^ k) (2 ^ n) :=
        Nat.Coprime.pow k n ((Nat.coprime_primes hr Nat.prime_two).mpr hr2)
      exact Nat.Coprime.eq_one_of_dvd hcop hdvd
  rw [hrk] at hk
  exact Subgroup.eq_bot_of_card_eq L hk

end CFSG.ShultStronglyClosedTI.SuzukiExclusion
