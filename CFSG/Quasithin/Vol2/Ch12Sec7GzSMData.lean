module

public import Certificates.Data.S1277MLine
public import Mathlib.Data.Finset.Card

public section

namespace CFSG.Quasithin.H13.I1277

open CFSG.Quasithin.H13.S127.Mod Certificates.Data.S1277MLine

theorem dedupAux_mem_iff (l : List ℕ) : ∀ (acc : List ℕ) (x : ℕ),
    x ∈ dedupAux acc l ↔ x ∈ acc ∨ x ∈ l := by
  induction l with
  | nil => intro acc x; simp [dedupAux]
  | cons y ys ih =>
    intro acc x
    cases hc : acc.contains y
    · have hy' : y ∉ acc := fun h' => by have h'' := List.contains_iff_mem.mpr h'; rw [hc] at h''; exact Bool.false_ne_true h''
      rw [dedupAux, hc]
      simp only [Bool.false_eq_true, if_false, ih, List.mem_cons]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
    · have hy' : y ∈ acc := List.contains_iff_mem.mp hc
      rw [dedupAux, hc]
      simp only [if_true, ih, List.mem_cons]
      constructor
      · rintro (h | h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl h
        · exact Or.inl (h ▸ hy')
        · exact Or.inr h

theorem dedupAux_nodup (l : List ℕ) : ∀ (acc : List ℕ), acc.Nodup → (dedupAux acc l).Nodup := by
  induction l with
  | nil => intro acc h; simpa [dedupAux] using h
  | cons y ys ih =>
    intro acc h
    cases hc : acc.contains y
    · have hy' : y ∉ acc := fun h' => by have h'' := List.contains_iff_mem.mpr h'; rw [hc] at h''; exact Bool.false_ne_true h''
      rw [dedupAux, hc]
      simp only [Bool.false_eq_true, if_false]
      exact ih (y :: acc) (List.nodup_cons.mpr ⟨hy', h⟩)
    · rw [dedupAux, hc]
      simp only [if_true]
      exact ih acc h

theorem mem_dedupN {l : List ℕ} {x : ℕ} : x ∈ dedupN l ↔ x ∈ l := by
  simp [dedupN, dedupAux_mem_iff]

theorem dedupN_nodup (l : List ℕ) : (dedupN l).Nodup :=
  dedupAux_nodup l [] List.nodup_nil

theorem length_dedupN (l : List ℕ) : (dedupN l).length = l.toFinset.card := by
  rw [← List.toFinset_card_of_nodup (dedupN_nodup l)]
  congr 1
  ext x
  simp [mem_dedupN]

theorem orbitSize_eq (G : List B6) (c : ℕ) :
    orbitSize G c = (G.map fun B => B.app c).toFinset.card := length_dedupN _

theorem mem_fixList {B : B6} {c : ℕ} : c ∈ fixList B ↔ c < 64 ∧ B.app c = c := by
  simp [fixList, List.mem_filter, List.mem_range]

theorem nodup_fixList (B : B6) : (fixList B).Nodup :=
  (List.nodup_range).filter _

theorem mem_invsD {Γ : List B6} {D : List ℕ} {B : B6} :
    B ∈ invsD Γ D ↔ B ∈ Γ ∧ isInv B = true ∧ ∀ d ∈ D, B.app d = d := by
  simp [invsD, List.mem_filter, List.all_eq_true]

theorem mem_stabD {Γ : List B6} {D : List ℕ} {B : B6} :
    B ∈ stabD Γ D ↔ B ∈ Γ ∧ ∀ d ∈ D, B.app d ∈ D := by
  simp [stabD, List.mem_filter, List.all_eq_true]

theorem mem_orbD {D : List ℕ} {n c : ℕ} : c ∈ orbD D n ↔ c ∈ D ∧ orbitSize gm6 c = n := by
  simp [orbD, List.mem_filter]

theorem isInv_iff {B : B6} : isInv B = true ↔ B.comp B = B6.id ∧ B ≠ B6.id := by
  simp [isInv]

theorem mCheck_fix {Γ : List B6} (h : mCheck Γ () = true) {B : B6} (hB : B ∈ Γ)
    (hi : isInv B = true) : (fixList B).length ≤ 16 := by
  simp only [mCheck, Bool.and_eq_true, List.all_eq_true] at h
  have := h.1 B hB
  simpa [hi] using this

theorem mCheck_perD {Γ : List B6} (h : mCheck Γ () = true) {B : B6} (hB : B ∈ Γ)
    (hi : isInv B = true) (h16 : (fixList B).length = 16) :
    (invsD Γ (fixList B)).length ≤ 3 ∧ ((invsD Γ (fixList B)).length = 3 →
      4 ≤ (orbD (fixList B) 18).length ∧
      (∀ t ∈ orbD (fixList B) 18, ∀ s ∈ orbD (fixList B) 18,
        ∃ B' ∈ stabD Γ (fixList B), B'.app t = s) ∧
      ∃ c ∈ orbD (fixList B) 45,
        9 ≤ (dedupN ((stabD Γ (fixList B)).map fun B' => B'.app c)).length) := by
  simp only [mCheck, Bool.and_eq_true, List.all_eq_true] at h
  have h2 := h.2 B hB
  simp only [hi, h16, Bool.true_and, beq_self_eq_true, Bool.not_true, Bool.false_or,
    perD, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.any_eq_true] at h2
  obtain ⟨h3, h4⟩ := h2
  refine ⟨h3, fun h3' => ?_⟩
  rcases h4 with h4 | ⟨⟨h5, h6⟩, h7⟩
  · omega
  · refine ⟨h5, fun t ht s hs => ?_, ?_⟩
    · have := h6 t ht s hs
      simpa [List.any_eq_true] using this
    · obtain ⟨c, hc, hc9⟩ := h7
      exact ⟨c, hc, hc9⟩

end CFSG.Quasithin.H13.I1277

end
