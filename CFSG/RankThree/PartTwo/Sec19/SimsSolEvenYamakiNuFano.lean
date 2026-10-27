module

public import CFSG.ClassicalInvolution.Q3.AE.Models

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven.YamakiRec

open CFSG.ClassicalInvolution.Q3.AE

private lemma card_noncollinear :
    Fintype.card {t : Fin 7 × Fin 7 × Fin 7 //
      ∀ s ∈ fanoLines, ¬ (t.1 ∈ s ∧ t.2.1 ∈ s ∧ t.2.2 ∈ s)} = 168 := by
  decide +kernel

private lemma exists_line_image {ρ : Equiv.Perm (Fin 7)} (hρ : ρ ∈ l32) {s : Finset (Fin 7)}
    (hs : s ∈ fanoLines) : ∃ s' ∈ fanoLines, ∀ y ∈ s, ρ y ∈ s' :=
  ⟨s.map ρ.toEmbedding, (hρ s hs).1, fun _ hy => Finset.mem_map_of_mem ρ.toEmbedding hy⟩

private lemma noncollinear_image {σ : Equiv.Perm (Fin 7)} (hσ : σ ∈ l32) :
    ∀ s ∈ fanoLines, ¬ (σ 0 ∈ s ∧ σ 1 ∈ s ∧ σ 2 ∈ s) := by
  rintro s hs ⟨h0, h1, h2⟩
  obtain ⟨s', hs', hmap⟩ := exists_line_image (inv_mem hσ) hs
  have hnc : ∀ s' ∈ fanoLines, ¬ (0 ∈ s' ∧ 1 ∈ s' ∧ 2 ∈ s') := by decide +kernel
  refine hnc s' hs' ⟨?_, ?_, ?_⟩
  · simpa using hmap _ h0
  · simpa using hmap _ h1
  · simpa using hmap _ h2

private lemma fix_third {ρ : Equiv.Perm (Fin 7)} (hρ : ρ ∈ l32) {a b c : Fin 7}
    (hline : ({a, b, c} : Finset (Fin 7)) ∈ fanoLines)
    (huniq : ∀ s ∈ fanoLines, a ∈ s → b ∈ s → ∀ x ∈ s, x = a ∨ x = b ∨ x = c)
    (hac : a ≠ c) (hbc : b ≠ c) (ha : ρ a = a) (hb : ρ b = b) : ρ c = c := by
  obtain ⟨s', hs', hmap⟩ := exists_line_image hρ hline
  have h1 : a ∈ s' := by simpa [ha] using hmap a (by simp)
  have h2 : b ∈ s' := by simpa [hb] using hmap b (by simp)
  rcases huniq s' hs' h1 h2 _ (hmap c (by simp)) with h | h | h
  · exact absurd (ρ.injective (h.trans ha.symm)) hac.symm
  · exact absurd (ρ.injective (h.trans hb.symm)) hbc.symm
  · exact h

private lemma eq_one_of_fix {ρ : Equiv.Perm (Fin 7)} (hρ : ρ ∈ l32) (h0 : ρ 0 = 0)
    (h1 : ρ 1 = 1) (h2 : ρ 2 = 2) : ρ = 1 := by
  have h3 : ρ 3 = 3 := fix_third hρ (a := 0) (b := 1) (c := 3) (by decide)
    (by decide +kernel) (by decide) (by decide) h0 h1
  have h4 : ρ 4 = 4 := fix_third hρ (a := 1) (b := 2) (c := 4) (by decide)
    (by decide +kernel) (by decide) (by decide) h1 h2
  have h6 : ρ 6 = 6 := fix_third hρ (a := 0) (b := 2) (c := 6) (by decide)
    (by decide +kernel) (by decide) (by decide) h0 h2
  have h5 : ρ 5 = 5 := fix_third hρ (a := 2) (b := 3) (c := 5) (by decide)
    (by decide +kernel) (by decide) (by decide) h2 h3
  ext x
  have hx : ∀ x : Fin 7, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 := by decide
  rcases hx x with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [h0, h1, h2, h3, h4, h5, h6]

theorem card_l32_le : Nat.card ↥l32 ≤ 168 := by
  let f : ↥l32 → {t : Fin 7 × Fin 7 × Fin 7 //
      ∀ s ∈ fanoLines, ¬ (t.1 ∈ s ∧ t.2.1 ∈ s ∧ t.2.2 ∈ s)} := fun σ =>
    ⟨((σ : Equiv.Perm (Fin 7)) 0, (σ : Equiv.Perm (Fin 7)) 1, (σ : Equiv.Perm (Fin 7)) 2),
      noncollinear_image σ.2⟩
  have hf : Function.Injective f := by
    intro σ τ h
    simp only [f, Subtype.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨e0, e1, e2⟩ := h
    have hρ : (τ : Equiv.Perm (Fin 7))⁻¹ * σ ∈ l32 := mul_mem (inv_mem τ.2) σ.2
    have key := eq_one_of_fix hρ (by simp [e0]) (by simp [e1]) (by simp [e2])
    exact Subtype.ext (inv_mul_eq_one.mp key).symm
  calc Nat.card ↥l32 ≤ Nat.card {t : Fin 7 × Fin 7 × Fin 7 //
        ∀ s ∈ fanoLines, ¬ (t.1 ∈ s ∧ t.2.1 ∈ s ∧ t.2.2 ∈ s)} :=
        Nat.card_le_card_of_injective f hf
    _ = 168 := by rw [Nat.card_eq_fintype_card]; exact card_noncollinear

theorem card_evenVec : Nat.card {v : Fin 7 → ZMod 2 // ∑ i, v i = 0} = 64 := by
  rw [Nat.card_eq_fintype_card]
  decide

end CFSG.RankThree.PartTwo.Sec19.SolEven.YamakiRec
