module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1KitGFin

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LargeExtraspecial.O62 CFSG.LargeExtraspecial.O62.Code

theorem s16c1g_exists_codes (Pa : AddSubgroup V₀) (h4 : Nat.card Pa = 4)
    (hsing : ∀ v ∈ Pa, qModel true v = 0) :
    ∃ a b : ℕ, a < 64 ∧ b < 64 ∧ s16c1g_isPlane a b = true ∧
      ∀ v : V₀, v ∈ Pa ↔ v ∈ s16c1g_plane a b := by
  classical
  have hadd : ∀ x : V₀, x + x = 0 := by
    intro x
    rw [← one_smul (ZMod 2) x, ← add_smul, show (1 : ZMod 2) + 1 = 0 by decide, zero_smul]
  have hvec0 : vec 0 = (0 : V₀) := by
    funext i
    simp [vec, bitZ]
  have hvecxor : ∀ m n : ℕ, vec (m ^^^ n) = vec m + vec n := by
    intro m n
    funext i
    simp [vec, bitZ_xor]
  have hcodes : ∀ u : V₀, ∃ n : Fin 64, vec (n : ℕ) = u := by decide +kernel
  have hnc : (Pa : Set V₀).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact h4
  obtain ⟨x, hxP, hx0⟩ : ∃ x ∈ Pa, x ≠ 0 := by
    by_contra hcon
    have hsub : (Pa : Set V₀) ⊆ {0} := fun v hv => by
      by_contra hv0
      exact hcon ⟨v, hv, hv0⟩
    have h1 := Set.ncard_le_ncard hsub (Set.finite_singleton 0)
    rw [Set.ncard_singleton] at h1
    omega
  obtain ⟨y, hyP, hy0, hyx⟩ : ∃ y ∈ Pa, y ≠ 0 ∧ y ≠ x := by
    by_contra hcon
    have hsub : (Pa : Set V₀) ⊆ {0, x} := by
      intro v hv
      by_cases h0 : v = 0
      · exact Or.inl h0
      · by_cases hx' : v = x
        · exact Or.inr hx'
        · exact absurd ⟨v, hv, h0, hx'⟩ hcon
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 : ({0, x} : Set V₀).ncard ≤ 2 :=
      (Set.ncard_insert_le _ _).trans (by simp)
    omega
  obtain ⟨a, rfl⟩ := hcodes x
  obtain ⟨b, rfl⟩ := hcodes y
  have hq : ∀ n : ℕ, vec n ∈ Pa → qB true n = false := by
    intro n hn
    have h1 := hsing _ hn
    rw [qModel_vec] at h1
    cases h : qB true n
    · rfl
    · rw [h] at h1
      exact absurd h1 (by simp)
  have hxyP : vec (a : ℕ) + vec (b : ℕ) ∈ Pa := Pa.add_mem hxP hyP
  have hxyne : vec (a : ℕ) + vec (b : ℕ) ≠ 0 := by
    intro h
    apply hyx
    calc vec (b : ℕ) = vec (a : ℕ) + vec (a : ℕ) + vec (b : ℕ) := by rw [hadd, zero_add]
      _ = vec (a : ℕ) + (vec (a : ℕ) + vec (b : ℕ)) := by rw [add_assoc]
      _ = vec (a : ℕ) := by rw [h, add_zero]
  refine ⟨a, b, a.isLt, b.isLt, ?_, ?_⟩
  · have ha0 : (a : ℕ) ≠ 0 := fun h => hx0 (by rw [h, hvec0])
    have hb0 : (b : ℕ) ≠ 0 := fun h => hy0 (by rw [h, hvec0])
    have hab : (a : ℕ) ≠ (b : ℕ) := fun h => hyx (by rw [h])
    have hqa := hq a hxP
    have hqb := hq b hyP
    have hqab := hq (a ^^^ b) (by rw [hvecxor]; exact hxyP)
    simp only [s16c1g_isPlane, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true']
    exact ⟨⟨⟨⟨⟨ha0, hb0⟩, hab⟩, hqa⟩, hqb⟩, hqab⟩
  · let T : Finset V₀ := {0, vec (a : ℕ), vec (b : ℕ), vec (a : ℕ) + vec (b : ℕ)}
    have hT4 : T.card = 4 := by
      have e1 : vec (a : ℕ) + vec (b : ℕ) ≠ vec (b : ℕ) := by
        intro h
        apply hx0
        calc vec (a : ℕ) = vec (a : ℕ) + vec (b : ℕ) + vec (b : ℕ) := by
              rw [add_assoc, hadd, add_zero]
          _ = vec (b : ℕ) + vec (b : ℕ) := by rw [h]
          _ = 0 := hadd _
      have e2 : vec (a : ℕ) ≠ vec (a : ℕ) + vec (b : ℕ) := by
        intro h
        apply hy0
        calc vec (b : ℕ) = vec (a : ℕ) + vec (a : ℕ) + vec (b : ℕ) := by rw [hadd, zero_add]
          _ = vec (a : ℕ) + (vec (a : ℕ) + vec (b : ℕ)) := by rw [add_assoc]
          _ = vec (a : ℕ) + vec (a : ℕ) := by rw [← h]
          _ = 0 := hadd _
      rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_singleton]
      · simpa using e1
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hyx.symm, e2⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hx0.symm, hy0.symm, hxyne.symm⟩
    have hTsub : (↑T : Set V₀) ⊆ (Pa : Set V₀) := by
      intro v hv
      simp only [T, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact Pa.zero_mem
      · exact hxP
      · exact hyP
      · exact hxyP
    have hTeq : (↑T : Set V₀) = (Pa : Set V₀) := by
      refine Set.eq_of_subset_of_ncard_le hTsub ?_ (Set.toFinite _)
      rw [hnc, Set.ncard_coe_finset, hT4]
    intro v
    constructor
    · intro hv
      have hvT : v ∈ (↑T : Set V₀) := by rw [hTeq]; exact hv
      simp only [T, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hvT
      rcases hvT with rfl | rfl | rfl | rfl
      · exact ⟨0, by simp [s16c1g_planeList], hvec0⟩
      · exact ⟨a, by simp [s16c1g_planeList], rfl⟩
      · exact ⟨b, by simp [s16c1g_planeList], rfl⟩
      · exact ⟨(a : ℕ) ^^^ (b : ℕ), by simp [s16c1g_planeList], hvecxor _ _⟩
    · rintro ⟨n, hn, rfl⟩
      simp only [s16c1g_planeList, List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl
      · rw [hvec0]; exact Pa.zero_mem
      · exact hxP
      · exact hyP
      · rw [hvecxor]; exact hxyP

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
