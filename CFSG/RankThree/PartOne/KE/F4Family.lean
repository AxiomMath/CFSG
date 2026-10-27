module

public import CFSG.RankThree.PartOne.KE.FamilyArith
import CFSG.RankThree.PartOne.S8.CatalogAssembly
import CFSG.RankThree.GroupTheory.SteinbergBMExceptionalComponentCentralization
import CFSG.RankThree.Chevalley.SteinbergCFHigherExceptionalDefiningComponent
import CFSG.RankThree.Chevalley.SteinbergBNSplitTorusComponentExclusion
import CFSG.RankThree.Chevalley.SteinbergBNNoninnerComponentNodes
public import CFSG.RankThree.PartOne.KE.Statements

public section

namespace CFSG.RankThree.PartOne.KE

open Subgroup CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.RankThree.LocalRank
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.Blueprint (ChevalleyExceptionalModel)
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.Chevalley
open scoped Pointwise

theorem exactF4FiniteOrder :
    ∀ (K : Type) [Field K] [Finite K],
      Nat.card (CFSG.Blueprint.Chevalley.adjointGroup .F4 K) =
        Nat.card K ^ 24 * (Nat.card K ^ 2 - 1) * (Nat.card K ^ 6 - 1) * (Nat.card K ^ 8 - 1) *
          (Nat.card K ^ 12 - 1) := by
  intro K _ _
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_F4, CFSG.Open.ordF4]
  ring

open CFSG.RankThree.GroupTheory.SteinbergBM in
theorem f4Complete_of_endpoints (hE : F4Endpoints) :
    F4CompleteActualQuotientComponentOddAction := by
  intro X _ _ p hp hp3 N _ hN hX E hE' hEc t ht ht1 L hL ℓ f hℓ hf hmod hEL hSL
  have hp2 : p ≠ 2 := by omega
  have hset := (CFSG.RankThree.GroupTheory.SteinbergBY.section_nine_residual_to_intersection hp hp2
    E).1 t ht ht1
  have hXL := commutator_le_normalizer_of_le hSL hEL
  have hodd_of_le : localCoreProduct p E t ≤ centralizer (L : Set (X ⧸ N)) →
      ComponentLocalCoreOddConclusion p E t L := fun hle =>
    componentLocalCoreOddConclusion_of_le_centralizer hset hle
  have hcoprime : ¬ p ∣ Nat.card (L ⧸ center L) → localCoreProduct p E t ≤ centralizer
      (L : Set (X ⧸ N)) := fun hpT =>
    (ordinary_exceptional_coprime_normalized_component_centralization
      hp hp3 hE' hEc ht ht1 hL hpT hEL hXL
      ⟨.F4, ℓ, f, Or.inr (Or.inl rfl), hmod⟩).2.2.2.2
  have hnonfaithful : E ⊓ centralizer (L : Set (X ⧸ N)) ≠ ⊥ →
      localCoreProduct p E t ≤ centralizer (L : Set (X ⧸ N)) := fun hC =>
    commutator_eq_bot_iff_le_centralizer.mp
      (CFSG.RankThree.Coprime.nonfaithful_plane_local_core_product_centralizes_component hp hE'
        hEc ht ht1 hL hXL hC).2.2
  have hnoninner : Finkelstein1977.automizer L ⟨t, hEL ht⟩ ∉
      (MulAut.conj : (L ⧸ center L) →* MulAut (L ⧸ center L)).range →
      localCoreProduct p E t ≤ centralizer (L : Set (X ⧸ N)) := by
    intro hnon
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      exact (even_F4_noninner_actual_component_local_core_product_centralizes hp hp3 hE' hEc ht
        ht1 hL hf hmod hEL hSL hnon).2
    · exact (odd_F4_noninner_actor_actual_component_local_core_product_centralizes hp hp2 hE' hEc
        ht ht1 hL hℓ hℓ2 hf hmod hEL hSL hnon).2
  have hcent : (¬ p ∣ Nat.card (L ⧸ center L) ∨ E ⊓ centralizer (L : Set (X ⧸ N)) ≠ ⊥ ∨
      Finkelstein1977.automizer L ⟨t, hEL ht⟩ ∉
        (MulAut.conj : (L ⧸ center L) →* MulAut (L ⧸ center L)).range) →
      localCoreProduct p E t ≤ centralizer (L : Set (X ⧸ N)) := by
    rintro (h | h | h)
    exacts [hcoprime h, hnonfaithful h, hnoninner h]
  refine ⟨?_, hcent⟩
  by_cases hpT : p ∣ Nat.card (L ⧸ center L)
  swap
  · exact hodd_of_le (hcoprime hpT)
  by_cases hC : E ⊓ centralizer (L : Set (X ⧸ N)) ≠ ⊥
  · exact hodd_of_le (hnonfaithful hC)
  have hℓp : ℓ ≠ p := by
    rintro rfl
    exact higher_ordinary_exceptional_defining_prime_actual_component_exclusion hp hp3 N hN hX L
      (Or.inl rfl) f hmod
  obtain ⟨hm1, hm2⟩ := F4_cross_prime_actual_component_toral_factor_restriction hp hp3 N hN hX L hℓ
    hmod
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  have h1 : ¬ (p : ℤ) ∣ cycloVal 1 ℓ f := not_dvd_cycloVal_one_of hq1 hm1
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := exists_mulEquiv_adjointGroup_of_untwisted hmod.2
  have hordT : Nat.card (L ⧸ center L) = (ℓ ^ f) ^ 24 * ((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 6 - 1) *
      ((ℓ ^ f) ^ 8 - 1) * ((ℓ ^ f) ^ 12 - 1) := by
    rw [← Nat.card_congr e.toEquiv, exactF4FiniteOrder K, hK]
  have hpdvd : p ∣ (ℓ ^ f) ^ 24 * ((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 6 - 1) * ((ℓ ^ f) ^ 8 - 1) *
      ((ℓ ^ f) ^ 12 - 1) := hordT ▸ hpT
  have hpq : ¬ p ∣ (ℓ ^ f) ^ 24 := fun h =>
    hℓp ((Nat.prime_dvd_prime_iff_eq hp hℓ).mp (hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow h))).symm
  have hprod : (p : ℤ) ∣ (((ℓ ^ f : ℕ) : ℤ) ^ 2 - 1) * (((ℓ ^ f : ℕ) : ℤ) ^ 6 - 1) *
      (((ℓ ^ f : ℕ) : ℤ) ^ 8 - 1) * (((ℓ ^ f : ℕ) : ℤ) ^ 12 - 1) := by
    have h0 : p ∣ ((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 6 - 1) * ((ℓ ^ f) ^ 8 - 1) *
        ((ℓ ^ f) ^ 12 - 1) := by
      rw [mul_assoc, mul_assoc, mul_assoc] at hpdvd
      rcases (Nat.Prime.dvd_mul hp).1 hpdvd with h | h
      · exact absurd h hpq
      · rwa [mul_assoc, mul_assoc]
    have h2' : (((((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 6 - 1) * ((ℓ ^ f) ^ 8 - 1) *
        ((ℓ ^ f) ^ 12 - 1) : ℕ)) : ℤ) = (((ℓ ^ f : ℕ) : ℤ) ^ 2 - 1) *
        (((ℓ ^ f : ℕ) : ℤ) ^ 6 - 1) * (((ℓ ^ f : ℕ) : ℤ) ^ 8 - 1) *
        (((ℓ ^ f : ℕ) : ℤ) ^ 12 - 1) := by
      have a2 : 1 ≤ (ℓ ^ f) ^ 2 := Nat.one_le_pow _ _ hq1
      have a6 : 1 ≤ (ℓ ^ f) ^ 6 := Nat.one_le_pow _ _ hq1
      have a8 : 1 ≤ (ℓ ^ f) ^ 8 := Nat.one_le_pow _ _ hq1
      have a12 : 1 ≤ (ℓ ^ f) ^ 12 := Nat.one_le_pow _ _ hq1
      push_cast [Nat.cast_sub a2, Nat.cast_sub a6, Nat.cast_sub a8, Nat.cast_sub a12]
      ring
    rw [← h2']
    exact_mod_cast h0
  have hd := F4_prime_dvd_cyclotomic hp hprod
  have app : ∀ {Cond : ℕ → ℕ → ℕ → Prop}, OddEndpoint .F4 Cond → Cond p ℓ f →
      ComponentLocalCoreOddConclusion p E t L := fun H hc =>
    H (X ⧸ N) p ℓ f hp hp3 hℓ hℓp hf hc E hE' hEc t ht ht1 L hL hmod hEL hSL
  by_cases hℓ2 : ℓ = 2
  · rcases hd with hd | hd | hd | hd | hd | hd | hd
    · exact absurd hd h1
    · exact app hE.evenQPlus ⟨hℓ2, hd⟩
    · exact app hE.evenPhi3 ⟨hℓ2, hd⟩
    · exact app hE.evenPhi4 ⟨hℓ2, hd⟩
    · exact app hE.evenPhi6 ⟨hℓ2, hd⟩
    · exact app hE.phi8Phi12 (Or.inl hd)
    · exact app hE.phi8Phi12 (Or.inr hd)
  · have h2 : ¬ (p : ℤ) ∣ cycloVal 2 ℓ f := not_dvd_cycloVal_two_of (hm2 hℓ2).1
    rcases hd with hd | hd | hd | hd | hd | hd | hd
    · exact absurd hd h1
    · exact absurd hd h2
    · exact app hE.oddPhi3Phi6 ⟨hℓ2, Or.inl hd⟩
    · exact app hE.oddPhi4 ⟨hℓ2, hd⟩
    · exact app hE.oddPhi3Phi6 ⟨hℓ2, Or.inr hd⟩
    · exact app hE.phi8Phi12 (Or.inl hd)
    · exact app hE.phi8Phi12 (Or.inr hd)

end CFSG.RankThree.PartOne.KE
