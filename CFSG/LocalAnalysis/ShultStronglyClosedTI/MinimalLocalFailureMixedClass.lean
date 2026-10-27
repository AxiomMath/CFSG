module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureMixedClassCentral

public section

namespace CFSG.ShultStronglyClosedTI.MixedClass

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ShultStronglyClosedTI
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_second_fixed_of_mem_class {H : Subgroup G} {beta : rightCosetSpace H}
    (hbeta : beta ≠ rightCosetMk H 1) {u : G} (huB : u ∈ pairPointStabilizer H beta) {v : G}
    (hv : v ∈ involutionPointClass u) :
    ∃ γ : rightCosetSpace H, γ ≠ rightCosetMk H 1 ∧ rightCosetTranslate H γ v = γ := by
  obtain ⟨x, rfl⟩ := hv
  have hα : rightCosetTranslate H (rightCosetMk H 1) u = rightCosetMk H 1 :=
    (mem_rightCosetStabilizer_iff H _ u).mp huB.1
  have hβ : rightCosetTranslate H beta u = beta := (mem_rightCosetStabilizer_iff H _ u).mp huB.2
  have hfix : ∀ ω : rightCosetSpace H, rightCosetTranslate H ω u = ω →
      rightCosetTranslate H (rightCosetTranslate H ω x) (x⁻¹ * u * x) =
        rightCosetTranslate H ω x := by
    intro ω hω
    rw [rightCosetTranslate_mul, show x * (x⁻¹ * u * x) = u * x by group,
      ← rightCosetTranslate_mul, hω]
  have hne : rightCosetTranslate H (rightCosetMk H 1) x ≠ rightCosetTranslate H beta x := by
    intro heq
    apply hbeta
    have h' := congrArg (fun ω => rightCosetTranslate H ω x⁻¹) heq
    simp only [rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one] at h'
    exact h'.symm
  by_cases hγ : rightCosetTranslate H (rightCosetMk H 1) x = rightCosetMk H 1
  · exact ⟨rightCosetTranslate H beta x, fun h' => hne (hγ.trans h'.symm), hfix beta hβ⟩
  · exact ⟨rightCosetTranslate H (rightCosetMk H 1) x, hγ, hfix _ hα⟩

theorem minimalLocalFailure_mixed_involution_class_closure
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {u : G} (huB : u ∈ pairPointStabilizer H beta) (hu : orderOf u = 2) :
    let Q := minimalLocalFailurePairActionPointHull H z
    let D := involutionPointClass z
    let U := involutionPointClass u
    let E := Q ⊓ Subgroup.centralizer ({u} : Set G)
    let Δ := (fun e => u * e) '' (E : Set G)
    U ∩ (H : Set G) = conjugacyWithin H u ∧ Δ ⊆ U ∧
      (∀ a ∈ Δ, ∀ b ∈ Δ, ∀ c ∈ Δ, ∀ d ∈ Δ, a ≠ b → c ≠ d →
        ∃ n ∈ H ⊓ Subgroup.normalizer Δ, n⁻¹ * a * n = c ∧ n⁻¹ * b * n = d) ∧
      (¬ Q ≤ Subgroup.centralizer ({u} : Set G) → Δ = conjugacyWithin Q u) ∧
      (∀ v ∈ U, ∀ r ∈ D, Commute v r → v * r ∈ U) ∧
      ¬ IsConj z u ∧
      ∀ v r : G, IsConj u v → IsConj z r → Commute v r → IsConj u (v * r) := by
  intro Q D U E Δ
  obtain ⟨hQ, hQ4, hQclass, -⟩ :=
    CyclicPair.proper_pair_cyclic_commutator h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨-, -, -, -, hnoncent, htransE, hΔorbit, -⟩ :=
    FixedPointModel.involution_centralizer_fixed_point_model h hcomm hsmallerR1 hbeta ht hproper
      huB hu
  have hdatum := h.local_datum
  have horbit : {omega : rightCosetSpace H | ∃ y ∈ Subgroup.centralizer ({u} : Set G),
      rightCosetTranslate H (rightCosetMk H 1) y = omega} =
      {omega : rightCosetSpace H | rightCosetTranslate H omega u = omega} := hΔorbit.symm
  have huH : u ∈ H := pairPointStabilizer_le_point H beta huB
  have hu2 : u * u = 1 := mul_self_eq_one_of_orderOf_eq_two hu
  have huD : u ∉ involutionPointClass z := not_mem_pointClass_of_two_fixed hdatum hbeta huB
  have hzu : ¬ IsConj z u := fun hc => huD (mem_pointClass_iff_isConj.mpr hc)
  have hQH : Q ≤ H := point_subgroup_le hdatum.distinguished_mem hQclass
  have huQ : ∀ v ∈ Q, u⁻¹ * v * u ∈ Q := point_subgroup_normalized hQclass u huH
  have hsqQ : ∀ a ∈ Q, a * a = 1 := fun a ha => by rw [← sq]; exact hQ.2 a ha
  have hQab : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hQ.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hΔU : Δ ⊆ U := by
    by_cases hQu : Q ≤ Subgroup.centralizer ({u} : Set G)
    · rintro x ⟨e, he, rfl⟩
      exact coset_subset_class_of_centralizing h hcomm hsmallerR1 hbeta ht hproper huB hu hQu
        e he.1
    · change (fun e => u * e) '' ((Q ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) :
        Set G) ⊆ involutionPointClass u
      rw [coset_eq_conjugacyWithin hQ hu2 huQ (hnoncent hQu)]
      rintro x ⟨q, rfl⟩
      exact ⟨q, rfl⟩
  have htrans : ∀ x ∈ Δ, ∃ n ∈ H ⊓ Subgroup.normalizer Δ, n⁻¹ * u * n = x := by
    by_cases hQu : Q ≤ Subgroup.centralizer ({u} : Set G)
    · have hE : E = Q := inf_eq_left.mpr hQu
      have hΔeq : Δ = (fun f => u * f) '' (Q : Set G) := by
        change (fun e => u * e) '' (E : Set G) = _
        rw [hE]
      rw [hΔeq]
      apply coset_transitive_of_centralizing hQclass hQ hQ4
      intro e he a ha b hb
      by_cases he1 : e = 1
      · rw [he1, mul_one]
        exact htransE a ⟨⟨ha.1, hQu ha.1⟩, ha.2⟩ b ⟨⟨hb.1, hQu hb.1⟩, hb.2⟩
      · have hvU : u * e ∈ U := hΔU ⟨e, ⟨he, hQu he⟩, rfl⟩
        obtain ⟨γ, hγα, hγ⟩ := exists_second_fixed_of_mem_class hbeta huB hvU
        have hcommu : ∀ f ∈ Q, u * f = f * u := fun f hf =>
          (Subgroup.mem_centralizer_singleton_iff.mp (hQu hf)).symm
        have hv2 : orderOf (u * e) = 2 := by
          apply orderOf_eq_prime
          · rw [sq, show u * e * (u * e) = u * (e * u) * e by group, ← hcommu e he,
              show u * (u * e) * e = (u * u) * (e * e) by group, hu2, hsqQ e he, one_mul]
          · intro h1
            apply huD
            have hu' : u = e⁻¹ := eq_inv_of_mul_eq_one_left h1
            rw [hu']
            exact point_subgroup_class hdatum hQclass
              ⟨Q.inv_mem he, fun h1 => he1 (inv_eq_one.mp h1)⟩
        have hQv : Q ≤ Subgroup.centralizer ({u * e} : Set G) := by
          intro a ha
          rw [Subgroup.mem_centralizer_singleton_iff,
            show a * (u * e) = (a * u) * e by group, ← hcommu a ha, mul_assoc, hQab a ha e he,
            ← mul_assoc]
        exact centralizer_transitive_of_second_fixed h hcomm hsmallerR1 hbeta ht hproper
          (H.mul_mem huH (hQH he)) hv2 hQv hγα hγ a ha b hb
    · have hΔeq : Δ = conjugacyWithin Q u := coset_eq_conjugacyWithin hQ hu2 huQ (hnoncent hQu)
      rw [hΔeq]
      rintro x ⟨q, rfl⟩
      exact ⟨q, ⟨hQH q.2, le_normalizer_conjugacyWithin Q u q.2⟩, rfl⟩
  have hmixed : ∀ v ∈ U, ∀ r ∈ D, Commute v r → v * r ∈ U := fun v hv r hr hvr =>
    mul_mem_of_coset_mem hdatum hQclass horbit (fun x hx g => conj_mem_pointClass hx g)
      (fun e he => hΔU ⟨e, he.1, rfl⟩) hv hr hvr
  refine ⟨class_inter_point_eq huH horbit, hΔU, coset_two_transitive hQclass htransE htrans,
    fun hQu => coset_eq_conjugacyWithin hQ hu2 huQ (hnoncent hQu), hmixed, hzu, ?_⟩
  intro v r hv hr hvr
  exact mem_pointClass_iff_isConj.mp (hmixed v (mem_pointClass_iff_isConj.mpr hv) r
    (mem_pointClass_iff_isConj.mpr hr) hvr)

end CFSG.ShultStronglyClosedTI.MixedClass
