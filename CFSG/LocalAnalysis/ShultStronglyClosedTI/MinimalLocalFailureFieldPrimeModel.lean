module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFieldPrimeHullCount
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFieldPrimeModelParameter
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFieldPrimeFlip
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFieldPrimeHull
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFieldPrimeLocal

public section

namespace CFSG.ShultStronglyClosedTI.CyclicSemiregular

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull
open CFSG.ProperTwoGeneratedCore.LocalCriterionDoubleTransitiveNormalizer
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField
open scoped MatrixGroups commutatorElement
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.ProperTwoGeneratedCore.LocalCriterionRecognizedThreePoint

universe u

variable {G : Type u} [Group G] [Finite G]

theorem baseOrbit_eq_hull {H Y : Subgroup G} {r : G} (hrY : r ∈ Y)
    (hlocalY : InvolutionPointLocalEmbedding (H.subgroupOf Y) (⟨r, hrY⟩ : Y)) :
    baseOrbit H Y = baseOrbit H (Subgroup.closure (conjugacyWithin Y r)) := by
  have hLY : Subgroup.closure (conjugacyWithin Y r) ≤ Y := by
    apply (Subgroup.closure_le _).mpr
    rintro w ⟨k, rfl⟩
    exact Y.mul_mem (Y.mul_mem (Y.inv_mem k.2) hrY) k.2
  obtain ⟨-, htrans, -⟩ := involution_point_hull_controls_class hlocalY
  have hmap := CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull.internal_hull_map Y hrY
  ext omega
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨l, hl⟩ := htrans (rightCosetMk (H.subgroupOf Y) 1)
      (rightCosetMk (H.subgroupOf Y) ⟨g, hg⟩)
    refine ⟨((l : Y) : G), ?_, ?_⟩
    · have hmem := Subgroup.mem_map_of_mem Y.subtype l.2
      rw [hmap] at hmem
      exact hmem
    · have himage := congrArg (restrictedRightCosetEmbedding H Y) hl
      rw [restrictedRightCosetEmbedding_translate, restrictedRightCosetEmbedding_base] at himage
      rw [himage]
      exact (translate_base_mk H g).symm
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hLY hg, rfl⟩

omit [Finite G] in
theorem involutionCore_closure_eq_top {S : Set G} (hS : ∀ s ∈ S, IsInvolution s) :
    involutionCore (Subgroup.closure S) = ⊤ := by
  apply top_unique
  rw [← Subgroup.closure_closure_coe_preimage (k := S)]
  apply Subgroup.closure_mono
  intro x hx
  have hxS := hS _ hx
  exact ⟨fun h1 => hxS.1 (congrArg Subtype.val h1), Subtype.ext (by simpa using hxS.2)⟩

theorem field_prime_hull_model {H : Subgroup G} {z : G}
    (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type u) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {Q : Subgroup G} (hQ : IsElemAbelian 2 Q)
    (hQclass : (Q : Set G) \ {1} = conjugacyWithin H z)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {y : G} (hY : Subgroup.centralizer ({y} : Set G) < ⊤)
    {ty : G} (hty : ty ∈ rightPairFlipFiber H z beta) (htyY : Commute ty y)
    {X₀ : Subgroup G} (hX₀ : X₀ ≤ H ⊓ Subgroup.centralizer ({y} : Set G))
    (htrans : ∀ a ∈ ((Q ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) : Set G) \ {1},
      ∀ b ∈ ((Q ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) : Set G) \ {1},
        ∃ x ∈ X₀, x⁻¹ * a * x = b)
    (hE4 : 4 ≤ Nat.card (Q ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G))
    {r : G} (hr : r ∈ Q ⊓ Subgroup.centralizer ({y} : Set G)) (hr1 : r ≠ 1) :
    let Y := Subgroup.centralizer ({y} : Set G)
    let E := Q ⊓ Y
    let L := Subgroup.closure (conjugacyWithin Y r)
    let R := (CFSG.oddCore Y).map Y.subtype
    let Δ := baseOrbit H Y
    2 ≤ twoRank L ∧ fusionStronglyEmbedded (H.subgroupOf L) ∧ R ≤ pairPointStabilizer H beta ∧
      ⁅R, L⁆ = ⊥ ∧ Δ = baseOrbit H L ∧
      ((∃ f : ℕ, 2 ≤ f ∧ 2 ^ f = Nat.card E ∧
          Nonempty (L ⧸ CFSG.oddCore L ≃* PSL(2, GaloisField 2 f)) ∧
          Nat.card Δ = Nat.card E + 1) ∨
        (∃ a : ℕ, 1 ≤ a ∧ 2 ^ (2 * a + 1) = Nat.card E ∧
          Nonempty (L ⧸ CFSG.oddCore L ≃* Sz a) ∧ Nat.card Δ = Nat.card E ^ 2 + 1) ∨
        (∃ f : ℕ, 2 ≤ f ∧ 2 ^ f = Nat.card E ∧
          Nonempty (L ⧸ CFSG.oddCore L ≃* PSU3 2 f) ∧ Nat.card Δ = Nat.card E ^ 3 + 1)) := by
  intro Y E L R Δ
  have htyH : ty ∉ H := rightPairFlipFiber_not_mem hbeta hty
  have htyYmem : ty ∈ Y := Subgroup.mem_centralizer_singleton_iff.mpr htyY.eq
  have hYH : ¬ Y ≤ H := fun hle => htyH (hle htyYmem)
  obtain ⟨hlocalY, -, -, hEL, -⟩ :=
    centralizer_class_data h.local_datum h.central_sylow hQclass hYH hX₀ htrans hr hr1
  obtain ⟨hM, -, hrank, hRL, hbender⟩ := centralizer_hull_rank_two h hcomm hsmallerR1 hQ
    hQclass hY hYH hr.1 hr1 hr.2 inf_le_left hEL hE4
  have hLY : L ≤ Y := by
    apply (Subgroup.closure_le _).mpr
    rintro w ⟨k, rfl⟩
    exact Y.mul_mem (Y.mul_mem (Y.inv_mem k.2) hr.2) k.2
  have hnorm : ∀ a ∈ Y, ∀ x ∈ L, a * x * a⁻¹ ∈ L :=
    fun a ha x hx => conj_mem_closure_conjugacyWithin ha hx
  obtain ⟨-, hcentral⟩ := oddCore_le_center_of_commutator hLY hnorm hRL
  have hrL : r ∈ L := Subgroup.subset_closure ⟨1, by simp⟩
  have hRcomm : ∀ g ∈ R, g * r = r * g := by
    intro g hg
    have hc : ⁅g, r⁆ ∈ ⁅R, L⁆ := Subgroup.commutator_mem_commutator hg hrL
    rw [hRL, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    exact hc
  have hrc : r ∈ conjugacyWithin H z := hQclass ▸ (⟨hr.1, hr1⟩ : r ∈ (Q : Set G) \ {1})
  obtain ⟨k, hk⟩ := hrc
  have hk' : rightConjugateElem z (k : G) = r := hk
  have hdatum : InvolutionPointLocalEmbedding H r := by
    have hl := local_point_datum_right_conjugate h.local_datum (k : G)
    rwa [minimalLocalFailure_point_right_conjugate H k k.2, hk'] at hl
  have hRH : R ≤ H := fun g hg =>
    point_centralizer_le hdatum (Subgroup.mem_centralizer_singleton_iff.mpr (hRcomm g hg))
  have hRB : R ≤ pairPointStabilizer H beta := by
    intro g hg
    refine ⟨?_, ?_⟩
    · rw [rightCosetStabilizer_base]
      exact hRH hg
    · have hconj : ty * g * ty⁻¹ ∈ R := conj_mem_oddCore_map hg htyYmem
      have hfix : rightCosetTranslate H (rightCosetMk H 1) (ty * g * ty⁻¹) = rightCosetMk H 1 :=
        (translate_base_iff H _).mpr (hRH hconj)
      apply (mem_rightCosetStabilizer_iff H beta g).mpr
      rw [← hty.2, rightCosetTranslate_mul]
      have heq : ty * g = (ty * g * ty⁻¹) * ty := by group
      rw [heq, ← rightCosetTranslate_mul, hfix]
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
  refine ⟨hrank, hM, hRB, hRL, hΔ, ?_⟩
  rcases hbender with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · obtain ⟨hidx, hcnt⟩ := linear_model_borel_parameter hf e _ hBorel
    have hq : 2 ^ f = Nat.card E := by
      have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      have h2 : 2 ^ f - 1 = Nat.card E - 1 := hcnt.symm.trans hcount
      omega
    exact Or.inl ⟨f, hf, hq, ⟨e⟩, by rw [← hindex, hidx, hq, pow_one]⟩
  · obtain ⟨hidx, hcnt⟩ := unitary_model_borel_parameter hf e _ hBorel
    have hq : 2 ^ f = Nat.card E := by
      have h1 : 1 ≤ 2 ^ f := Nat.one_le_two_pow
      have h2 : 2 ^ f - 1 = Nat.card E - 1 := hcnt.symm.trans hcount
      omega
    exact Or.inr (Or.inr ⟨f, hf, hq, ⟨e⟩, by rw [← hindex, hidx, hq]⟩)
  · obtain ⟨hidx, hcnt⟩ := suzuki_model_borel_parameter ha e _ hBorel
    have hq : 2 ^ (2 * a + 1) = Nat.card E := by
      have h1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
      have h2 : 2 ^ (2 * a + 1) - 1 = Nat.card E - 1 := hcnt.symm.trans hcount
      omega
    exact Or.inr (Or.inl ⟨a, ha, hq, ⟨e⟩, by rw [← hindex, hidx, hq]⟩)

end CFSG.ShultStronglyClosedTI.CyclicSemiregular
