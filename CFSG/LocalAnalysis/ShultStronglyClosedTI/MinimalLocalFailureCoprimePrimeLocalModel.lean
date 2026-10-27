module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureCoprimePrimeLocalClass
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFieldPrimeModel

public section

namespace CFSG.ShultStronglyClosedTI.CoprimePrime

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePoint
open CFSG.ShultStronglyClosedTI.CyclicSemiregular

variable {G : Type} [Group G] [Finite G]

theorem subgroup_orbit_degree {H : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {Q : Subgroup G} (hQ : IsElemAbelian 2 Q)
    (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z)
    {Y : Subgroup G} (hY : Y < ⊤) (hYH : ¬ Y ≤ H)
    {X₀ : Subgroup G} (hX₀ : X₀ ≤ H ⊓ Y)
    (htrans : ∀ a ∈ ((Q ⊓ Y : Subgroup G) : Set G) \ {1},
      ∀ b ∈ ((Q ⊓ Y : Subgroup G) : Set G) \ {1}, ∃ x ∈ X₀, x⁻¹ * a * x = b)
    (hE4 : 4 ≤ Nat.card (Q ⊓ Y : Subgroup G))
    {r : G} (hr : r ∈ Q ⊓ Y) (hr1 : r ≠ 1) :
    ∃ i : ℕ, (i = 1 ∨ i = 2 ∨ i = 3) ∧
      Nat.card (baseOrbit H Y) = Nat.card (Q ⊓ Y : Subgroup G) ^ i + 1 := by
  set E := Q ⊓ Y
  set L := Subgroup.closure (conjugacyWithin Y r)
  set Δ := baseOrbit H Y
  obtain ⟨hlocalY, -, -, hEL, -⟩ :=
    subgroup_class_data h.local_datum h.central_sylow hQclass hYH hX₀ htrans hr hr1
  obtain ⟨hM, -, hrank, hRL, hbender⟩ := centralizer_hull_rank_two h hcomm hsmallerR1 hQ
    hQclass hY hYH hr.1 hr1 hr.2 inf_le_left hEL hE4
  have hLY : L ≤ Y := by
    apply (Subgroup.closure_le _).mpr
    rintro w ⟨k, rfl⟩
    exact Y.mul_mem (Y.mul_mem (Y.inv_mem k.2) hr.2) k.2
  have hnorm : ∀ a ∈ Y, ∀ x ∈ L, a * x * a⁻¹ ∈ L :=
    fun a ha x hx => conj_mem_closure_conjugacyWithin ha hx
  obtain ⟨-, hcentral⟩ := oddCore_le_center_of_commutator hLY hnorm hRL
  have hΔ : Δ = baseOrbit H L := baseOrbit_eq_hull hr.2 hlocalY
  have hcore : involutionCore L = ⊤ := by
    apply involutionCore_closure_eq_top
    rintro s ⟨a, rfl⟩
    exact isInvolution_rightConjugateElem ⟨hr1, by simpa using hQ.2 r hr.1⟩
  obtain ⟨-, hcoreM, hBorel⟩ :=
    CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator.whole_involution_core_native_model_and_borel
      (H.subgroupOf L) hM
      (native_rank_two_of_two_le_twoRank hrank) hcore
  have hindex : ((H.subgroupOf L).map (QuotientGroup.mk' (CFSG.oddCore L))).index =
      Nat.card Δ := by
    rw [Subgroup.index_map_eq (H.subgroupOf L) (QuotientGroup.mk'_surjective (CFSG.oddCore L))
      (by rw [QuotientGroup.ker_mk']; exact hcoreM), hΔ, card_baseOrbit]
  have hcount : Nat.card {x : L ⧸ CFSG.oddCore L //
      x ∈ (H.subgroupOf L).map (QuotientGroup.mk' (CFSG.oddCore L)) ∧ IsInvolution x} =
      Nat.card E - 1 := by
    rw [card_involutions_map_oddCore _ hcoreM hcentral]
    exact hull_point_involution_card h.local_datum hQ hQclass hr.1 hr1 hr.2 hM hEL
  have hE1 : 1 ≤ Nat.card E := Nat.card_pos
  rcases hbender with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · obtain ⟨hidx, hcnt⟩ := linear_model_borel_parameter hf e _ hBorel
    have hq : 2 ^ f = Nat.card E := by
      have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      have h2 : 2 ^ f - 1 = Nat.card E - 1 := hcnt.symm.trans hcount
      omega
    exact ⟨1, Or.inl rfl, by rw [← hindex, hidx, hq, pow_one]⟩
  · obtain ⟨hidx, hcnt⟩ := unitary_model_borel_parameter hf e _ hBorel
    have hq : 2 ^ f = Nat.card E := by
      have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      have h2 : 2 ^ f - 1 = Nat.card E - 1 := hcnt.symm.trans hcount
      omega
    exact ⟨3, Or.inr (Or.inr rfl), by rw [← hindex, hidx, hq]⟩
  · obtain ⟨hidx, hcnt⟩ := suzuki_model_borel_parameter ha e _ hBorel
    have hq : 2 ^ (2 * a + 1) = Nat.card E := by
      have h1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
      have h2 : 2 ^ (2 * a + 1) - 1 = Nat.card E - 1 := hcnt.symm.trans hcount
      omega
    exact ⟨2, Or.inr (Or.inl rfl), by rw [← hindex, hidx, hq]⟩

end CFSG.ShultStronglyClosedTI.CoprimePrime
