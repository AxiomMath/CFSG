module

public import CFSG.Quasithin.Background.B3Comp
public import CFSG.Quasithin.Background.B3Basic
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.Quasithin.B3

@[expose] def memD (D : List (List Tab)) (X : List Tab) : Bool :=
  D.any (fun B => B.length == X.length && seteqT B X)

theorem memD_spec {D : List (List Tab)} {X : List Tab} (h : memD D X = true) :
    ∃ B ∈ D, ∀ t, t ∈ B ↔ t ∈ X := by
  simp only [memD, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨B, hB, -, hs⟩ := h
  refine ⟨B, hB, fun t => ?_⟩
  simp only [seteqT, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hs
  exact ⟨fun ht => hs.1 t ht, fun ht => hs.2 t ht⟩

@[expose] def chkEA (n : ℕ) (T : List Tab) (D : List (List Tab)) : Bool :=
  memD D [idT n] &&
  D.all (fun A => subOK n A && A.all (fun a => T.contains a) &&
      A.all (fun a => A.all (fun b => mulT a b == mulT b a)) &&
      A.all (fun a => mulT a a == idT n)) &&
  D.all (fun A => T.all (fun s => !(mulT s s == idT n) || A.contains s ||
      !(A.all (fun a => mulT a s == mulT s a)) || memD D (extT A s)))

theorem chkEA_spec {n : ℕ} {T : List Tab} {D : List (List Tab)} (h : chkEA n T D = true) :
    (∃ B ∈ D, ∀ t, t ∈ B ↔ t = idT n) ∧
    (∀ A ∈ D, subOK n A = true ∧ (∀ a ∈ A, a ∈ T) ∧
      (∀ a ∈ A, ∀ b ∈ A, mulT a b = mulT b a) ∧ (∀ a ∈ A, mulT a a = idT n)) ∧
    (∀ A ∈ D, ∀ s ∈ T, mulT s s = idT n → s ∉ A → (∀ a ∈ A, mulT a s = mulT s a) →
      ∃ B ∈ D, ∀ t, t ∈ B ↔ t ∈ extT A s) := by
  simp only [chkEA, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨B, hB, hBt⟩ := memD_spec h1
    exact ⟨B, hB, fun t => by rw [hBt t]; simp⟩
  · intro A hA
    obtain ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩ := h2 A hA
    exact ⟨a1, a2, fun a ha b hb => a3 a ha b hb, a4⟩
  · intro A hA s hs hss hsA hcomm
    have h4 := h3 A hA s hs
    simp only [Bool.or_eq_true, Bool.not_eq_true'] at h4
    rcases h4 with ((h | h) | h) | h
    · simp only [beq_eq_false_iff_ne] at h
      exact absurd hss h
    · exact absurd (List.contains_iff_mem.1 h) hsA
    · have hall : A.all (fun a => mulT a s == mulT s a) = true := by
        simp only [List.all_eq_true, beq_iff_eq]
        exact hcomm
      rw [hall] at h
      exact absurd h (by simp)
    · exact memD_spec h

section Sound

variable {n : ℕ}

noncomputable def finOf (n : ℕ) (A : List Tab) : Finset (Gp n) := by
  classical
  exact Finset.univ.filter (fun σ => tab σ ∈ A)

theorem mem_finOf {A : List Tab} {σ : Gp n} : σ ∈ finOf n A ↔ tab σ ∈ A := by
  classical
  simp [finOf]

theorem exists_mem_D {T : List Tab} {D : List (List Tab)} (hT : subOK n T = true)
    (hD : chkEA n T D = true) (K : Subgroup (Gp n)) (hKT : ∀ x ∈ K, tab x ∈ T)
    (hcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) (hsq : ∀ a ∈ K, a * a = 1) :
    ∃ A ∈ D, subOK n A = true ∧ ∀ x : Gp n, x ∈ K ↔ tab x ∈ A := by
  classical
  obtain ⟨hid, hmem, hext⟩ := chkEA_spec hD
  obtain ⟨hTtab, -, -, -, -⟩ := subOK_spec hT
  have key := exists_mem_of_isEA_le (G := Gp n) (subOf n T) (D.map (finOf n)) ?_ ?_ K
    (fun x hx => (mem_subOf hT).2 (hKT x hx)) hcomm hsq
  · obtain ⟨A', hA'D, hA'⟩ := key
    obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hA'D
    exact ⟨A, hA, (hmem A hA).1, fun x => by rw [← mem_finOf, hA']⟩
  · obtain ⟨B, hB, hBt⟩ := hid
    refine List.mem_map.2 ⟨B, hB, ?_⟩
    ext σ
    simp only [mem_finOf, hBt, Finset.mem_singleton]
    rw [← tab_one]
    exact ⟨fun h => tab_injective h, fun h => by rw [h]⟩
  · intro A' hA' s hs hss hsA' hcommA'
    obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hA'
    rw [mem_subOf hT] at hs
    have hss' : mulT (tab s) (tab s) = idT n := by rw [← tab_mul, hss, tab_one]
    have hsA : tab s ∉ A := fun h => hsA' (mem_finOf.2 h)
    have hcommA : ∀ a ∈ A, mulT a (tab s) = mulT (tab s) a := by
      intro a ha
      obtain ⟨-, hAT, -, -⟩ := hmem A hA
      obtain ⟨a', rfl⟩ := exists_tab_eq (hTtab a (hAT a ha))
      have := hcommA' a' (mem_finOf.2 ha)
      rw [← tab_mul, ← tab_mul, this]
    obtain ⟨B, hB, hBt⟩ := hext A hA (tab s) hs hss' hsA hcommA
    refine List.mem_map.2 ⟨B, hB, ?_⟩
    ext σ
    simp only [mem_finOf, hBt, extT, List.mem_append, List.mem_map, Finset.mem_union,
      Finset.mem_image]
    constructor
    · rintro (h | ⟨a, ha, hσ⟩)
      · exact Or.inl h
      · right
        obtain ⟨-, hAT, -, -⟩ := hmem A hA
        obtain ⟨a', rfl⟩ := exists_tab_eq (hTtab a (hAT a ha))
        refine ⟨a', ha, ?_⟩
        apply tab_injective
        rw [tab_mul, hσ]
    · rintro (h | ⟨a', ha', rfl⟩)
      · exact Or.inl h
      · right
        exact ⟨tab a', ha', by rw [tab_mul]⟩

end Sound

end CFSG.Quasithin.B3
