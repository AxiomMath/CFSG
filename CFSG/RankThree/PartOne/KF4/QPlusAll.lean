module

public import CFSG.RankThree.PartOne.KF4.QPlusA2

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KE
open scoped Matrix Pointwise


section All

variable {L : Type} [Field L] [CharP L 2] [IsAlgClosed L] {K : Type} [Field K] [Finite K]
  [Algebra K L] [IsAlgClosure K L]

omit
  [IsAlgClosure K L] in
theorem qpK_facts (f : ℕ) (hk : Nat.card K = 2 ^ f) :
    (∀ a : K, iterateFrobenius L 2 f (algebraMap K L a) = algebraMap K L a) ∧
      Nat.card (qpK L f) = Nat.card K ∧ Finite (qpK L f) := by
  have hFr : ∀ c, iterateFrobenius L 2 f c = c ^ Nat.card K := fun c => by
    rw [hk, iterateFrobenius_def]
  have hK : ∀ a : K, iterateFrobenius L 2 f (algebraMap K L a) = algebraMap K L a := fun a =>
    DFunLike.congr_fun (frobenius_comp_algebraMap (k := K) (iterateFrobenius L 2 f) hFr) a
  have hmem : ∀ c : L, c ∈ qpK L f ↔ c ∈ Set.range (algebraMap K L) := fun c => by
    constructor
    · intro h
      have h' : iterateFrobenius L 2 f c = c := h
      rw [hFr] at h'
      exact mem_range_algebraMap_of_pow_card_eq h'
    · rintro ⟨a, rfl⟩
      exact hK a
  have hset : ((qpK L f : Subfield L) : Set L) = Set.range (algebraMap K L) :=
    Set.ext hmem
  have hcard : Nat.card (qpK L f) = Nat.card K := by
    have : Nat.card ↥((qpK L f : Subfield L) : Set L) = Nat.card K := by
      rw [hset]
      exact Nat.card_range_of_injective (algebraMap K L).injective
    exact this
  refine ⟨hK, hcard, Nat.finite_of_card_ne_zero ?_⟩
  rw [hcard]
  exact Nat.card_pos.ne'

theorem finset_fin4_cases (J : Finset (Fin Tag.F4.rank)) (h0 : J ≠ ∅)
    (h1 : J ≠ Finset.univ) :
    J = {f4Index 0} ∨ J = {f4Index 1} ∨ J = {f4Index 2} ∨ J = {f4Index 3} ∨
      J = {f4Index 0, f4Index 1} ∨ J = {f4Index 0, f4Index 2} ∨ J = {f4Index 0, f4Index 3} ∨
      J = {f4Index 1, f4Index 2} ∨ J = {f4Index 1, f4Index 3} ∨ J = {f4Index 2, f4Index 3} ∨
      J = {f4Index 0, f4Index 1, f4Index 2} ∨ J = {f4Index 0, f4Index 1, f4Index 3} ∨
      J = {f4Index 0, f4Index 2, f4Index 3} ∨ J = {f4Index 1, f4Index 2, f4Index 3} := by
  revert J
  decide +kernel

theorem qp_checks_A1A1 :
    qpOrthSuppB {f4Index 0} {f4Index 2} = true ∧
      qpUnionB {f4Index 0, f4Index 2} {f4Index 0} {f4Index 2} = true ∧
      qpA1B (f4Index 2) = true ∧
    qpOrthSuppB {f4Index 0} {f4Index 3} = true ∧
      qpUnionB {f4Index 0, f4Index 3} {f4Index 0} {f4Index 3} = true ∧
      qpA1B (f4Index 3) = true ∧
    qpOrthSuppB {f4Index 1} {f4Index 3} = true ∧
      qpUnionB {f4Index 1, f4Index 3} {f4Index 1} {f4Index 3} = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem qp_conn_checks :
    (∀ i ∈ (({f4Index 1, f4Index 2} : Finset (Fin Tag.F4.rank)) : Set (Fin Tag.F4.rank)),
      ∀ j ∈ (({f4Index 1, f4Index 2} : Finset (Fin Tag.F4.rank)) : Set (Fin Tag.F4.rank)),
      ∀ k : Fin Tag.F4.rank, i ≤ k → k ≤ j →
        k ∈ (({f4Index 1, f4Index 2} : Finset (Fin Tag.F4.rank)) : Set (Fin Tag.F4.rank))) ∧
    (∀ i ∈ (({f4Index 0, f4Index 1, f4Index 2} : Finset (Fin Tag.F4.rank)) :
        Set (Fin Tag.F4.rank)),
      ∀ j ∈ (({f4Index 0, f4Index 1, f4Index 2} : Finset (Fin Tag.F4.rank)) :
        Set (Fin Tag.F4.rank)), ∀ k : Fin Tag.F4.rank, i ≤ k → k ≤ j →
        k ∈ (({f4Index 0, f4Index 1, f4Index 2} : Finset (Fin Tag.F4.rank)) :
          Set (Fin Tag.F4.rank))) ∧
    (∀ i ∈ (({f4Index 1, f4Index 2, f4Index 3} : Finset (Fin Tag.F4.rank)) :
        Set (Fin Tag.F4.rank)),
      ∀ j ∈ (({f4Index 1, f4Index 2, f4Index 3} : Finset (Fin Tag.F4.rank)) :
        Set (Fin Tag.F4.rank)), ∀ k : Fin Tag.F4.rank, i ≤ k → k ≤ j →
        k ∈ (({f4Index 1, f4Index 2, f4Index 3} : Finset (Fin Tag.F4.rank)) :
          Set (Fin Tag.F4.rank))) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Finset.mem_coe] <;> decide +kernel

theorem qp_family_exists (f : ℕ) (hf : 1 ≤ f) (hk : Nat.card K = 2 ^ f) (hq : 4 ≤ 2 ^ f)
    (J : Finset (Fin Tag.F4.rank)) (h0 : J ≠ ∅) (h1 : J ≠ Finset.univ) :
    ∃ i₀ : Fin Tag.F4.rank, QPFam L K f J i₀ := by
  obtain ⟨hK, hcard, hfin⟩ := qpK_facts (L := L) (K := K) f hk
  have h4 : 4 ≤ Nat.card (qpK L f) := by rw [hcard, hk]; exact hq
  have hq2 : 2 < 2 ^ f := by omega
  have hne : ∀ c : Fin Tag.F4.rank, (({c} : Finset (Fin Tag.F4.rank)) :
      Set (Fin Tag.F4.rank)).Nonempty := fun c => ⟨c, by simp⟩
  obtain ⟨hcB2, hc012, hc123⟩ := qp_conn_checks
  obtain ⟨o02, u02, a2, o03, u03, a3, o13, u13⟩ := qp_checks_A1A1
  rcases finset_fin4_cases J h0 h1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · exact ⟨f4Index 0, qpFam_connected f h4 hK hf qpCascade_0 (hne _) (connected_singleton _)
      (Finset.mem_singleton_self _)⟩
  · exact ⟨f4Index 1, qpFam_connected f h4 hK hf qpCascade_1 (hne _) (connected_singleton _)
      (Finset.mem_singleton_self _)⟩
  · exact ⟨f4Index 2, qpFam_connected f h4 hK hf qpCascade_2 (hne _) (connected_singleton _)
      (Finset.mem_singleton_self _)⟩
  · exact ⟨f4Index 3, qpFam_connected f h4 hK hf qpCascade_3 (hne _) (connected_singleton _)
      (Finset.mem_singleton_self _)⟩
  · exact ⟨f4Index 0, qpFam_A2_long f hf hk hq2⟩
  · exact ⟨f4Index 2, qpFam_A1A1 f h4 hK hf qpCascade_0 qpCascade_2 o02 u02 a2⟩
  · exact ⟨f4Index 3, qpFam_A1A1 f h4 hK hf qpCascade_0 qpCascade_3 o03 u03 a3⟩
  · exact ⟨f4Index 1, qpFam_connected f h4 hK hf qpCascade_12 ⟨f4Index 1, by simp⟩ hcB2
      (i₀ := f4Index 1) (by simp)⟩
  · exact ⟨f4Index 3, qpFam_A1A1 f h4 hK hf qpCascade_1 qpCascade_3 o13 u13 a3⟩
  · exact ⟨f4Index 2, qpFam_A2_short f hf hk hq2⟩
  · exact ⟨f4Index 0, qpFam_connected f h4 hK hf qpCascade_012 ⟨f4Index 0, by simp⟩ hc012
      (i₀ := f4Index 0) (by simp)⟩
  · exact ⟨f4Index 3, qpFam_A2A1_long f hf hk hq2 h4 hK⟩
  · exact ⟨f4Index 0, qpFam_A2A1_short f hf hk hq2 h4 hK⟩
  · exact ⟨f4Index 1, qpFam_connected f h4 hK hf qpCascade_123 ⟨f4Index 1, by simp⟩ hc123
      (i₀ := f4Index 1) (by simp)⟩

end All

end CFSG.RankThree.PartOne.KF4
