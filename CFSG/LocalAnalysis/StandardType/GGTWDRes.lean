module

public import CFSG.LocalAnalysis.StandardType.GGTWDCells

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGTWDRes2 (p N : ℕ) : Prop :=
  ∀ (pos : GGTWPos) (c : Fin (N - 1)), GGTWPat2 N pos c.val none →
    ∀ ha1 αa1 ha2 αa2 : GGDepAE p N, GGTWDPairs2 p N pos c none ha1 αa1 ha2 αa2 →
      ggDepAdot αa1 (ggDepAx p N) = 0 → ggDepAdot αa2 (ggDepAx p N) ≠ 0 →
        ∃ g ∈ Submonoid.closure (Set.range (fun i : Fin (N - 1) =>
            ggDepARefl (ggDepAh p N i) (ggDepAα p N i)) ∪
              {ggDepARefl ha1 αa1, ggDepARefl ha2 αa2}), GGDepAIsTv g

@[expose] def GGTWDCertCells (p N : ℕ) : Prop :=
  GGTWDCells1 p N ∧ GGTWDRes2 p N

private lemma l05nD5_pat1_of_pat2 {N : ℕ} {pos : GGTWPos} {c : ℕ}
    {c₂ : Option (Fin (N - 1))} (h : GGTWPat2 N pos c (c₂.map Fin.val)) :
    GGTWPat1 N pos c (-1) (-1) := by
  unfold GGTWPat2 at h
  unfold GGTWPat1
  exact ⟨h.1, Or.inl ⟨h.2.1, Or.inl ⟨rfl, rfl⟩⟩⟩

private lemma l05nD5_pat1_of_pat2_some {N : ℕ} {pos : GGTWPos} {c c' : ℕ}
    (h : GGTWPat2 N pos c (some c')) : GGTWPat1 N pos c' (-1) (-1) := by
  unfold GGTWPat2 at h
  unfold GGTWPat1
  obtain ⟨-, -, hsome⟩ := h
  simp only at hsome
  obtain ⟨hin, hcase⟩ := hsome
  rcases hcase with ⟨-, h⟩ | ⟨-, h⟩
  · exact ⟨hin, Or.inl ⟨Or.inr h, Or.inl ⟨rfl, rfl⟩⟩⟩
  · exact ⟨hin, Or.inl ⟨Or.inl h, Or.inl ⟨rfl, rfl⟩⟩⟩

private lemma l05nD5_pairs1_left {p N : ℕ} {pos : GGTWPos} {c : Fin (N - 1)}
    {c₂ : Option (Fin (N - 1))} {ha1 αa1 ha2 αa2 : GGDepAE p N}
    (h : GGTWDPairs2 p N pos c c₂ ha1 αa1 ha2 αa2) :
    GGTWDPairs1 p N pos c (-1) (-1) ha1 αa1 := by
  intro c' hc'
  obtain ⟨hblock, -⟩ := h
  obtain ⟨h1, h2, -, -⟩ := hblock c' hc'
  exact ⟨by simpa using h1, by simpa using h2⟩

private lemma l05nD5_pairs1_right {p N : ℕ} {pos : GGTWPos} {c c' : Fin (N - 1)}
    {ha1 αa1 ha2 αa2 : GGDepAE p N}
    (h : GGTWDPairs2 p N pos c (some c') ha1 αa1 ha2 αa2) :
    GGTWDPairs1 p N pos c' (-1) (-1) ha2 αa2 := by
  intro c'' hc''
  obtain ⟨hblock, -⟩ := h
  obtain ⟨-, -, h3, h4⟩ := hblock c'' hc''
  exact ⟨by simpa [Option.some.injEq] using h3, by simpa [Option.some.injEq] using h4⟩

theorem ggTWD_cells2_of_cells1_res {p N : ℕ} (h1 : GGTWDCells1 p N) (h2 : GGTWDRes2 p N) :
    GGTWDCells2 p N := by
  unfold GGTWDCells2
  intro pos c c₂ hpat ha1 αa1 ha2 αa2 hpairs hx
  by_cases h1x : ggDepAdot αa1 (ggDepAx p N) = 0
  · have h2x : ggDepAdot αa2 (ggDepAx p N) ≠ 0 := by
      rcases hx with hx | hx
      · exact absurd h1x hx
      · exact hx
    cases c₂ with
    | none =>
        exact h2 pos c hpat ha1 αa1 ha2 αa2 hpairs h1x h2x
    | some c' =>
        have h22 : ggDepAdot αa2 ha2 = 2 := by
          obtain ⟨-, -, -, -, h22⟩ := hpairs; exact h22
        obtain ⟨g, hg, htv⟩ :=
          h1 pos c' (-1) (-1) (l05nD5_pat1_of_pat2_some hpat) ha2 αa2
            (l05nD5_pairs1_right hpairs) h22 h2x
        exact ⟨g, Submonoid.closure_mono (Set.union_subset_union_right _ (by
          intro x hx; exact Or.inr hx)) hg, htv⟩
  · have hpat1 : GGTWPat1 N pos c.val (-1) (-1) := l05nD5_pat1_of_pat2 hpat
    have h11 : ggDepAdot αa1 ha1 = 2 := by
      obtain ⟨-, -, -, h11, -⟩ := hpairs; exact h11
    obtain ⟨g, hg, htv⟩ :=
      h1 pos c (-1) (-1) hpat1 ha1 αa1 (l05nD5_pairs1_left hpairs) h11 h1x
    exact ⟨g, Submonoid.closure_mono (Set.union_subset_union_right _ (by
      intro x hx; exact Or.inl hx)) hg, htv⟩

theorem ggTWDCells_of_cert {p N : ℕ} (h : GGTWDCertCells p N) : GGTWDCells p N :=
  ⟨h.1, ggTWD_cells2_of_cells1_res h.1 h.2⟩

@[expose] def GGTWDCellsOr (p N : ℕ)
    (Out : Set (Module.End (ZMod p) (GGDepAE p N)) → Prop) : Prop :=
  (∀ (pos : GGTWPos) (c0 : Fin (N - 1)) (m n : ℤ), GGTWPat1 N pos c0.val m n →
    ∀ ha αa : GGDepAE p N, GGTWDPairs1 p N pos c0 m n ha αa → ggDepAdot αa ha = 2 →
      ggDepAdot αa (ggDepAx p N) ≠ 0 →
        (∃ g ∈ Submonoid.closure (Set.range (fun i : Fin (N - 1) =>
            ggDepARefl (ggDepAh p N i) (ggDepAα p N i)) ∪ {ggDepARefl ha αa}), GGDepAIsTv g) ∨
          Out (Set.range (fun i : Fin (N - 1) =>
            ggDepARefl (ggDepAh p N i) (ggDepAα p N i)) ∪ {ggDepARefl ha αa})) ∧
  (∀ (pos : GGTWPos) (c : Fin (N - 1)) (c₂ : Option (Fin (N - 1))),
    GGTWPat2 N pos c.val (c₂.map Fin.val) →
      ∀ ha1 αa1 ha2 αa2 : GGDepAE p N, GGTWDPairs2 p N pos c c₂ ha1 αa1 ha2 αa2 →
        (ggDepAdot αa1 (ggDepAx p N) ≠ 0 ∨ ggDepAdot αa2 (ggDepAx p N) ≠ 0) →
          (∃ g ∈ Submonoid.closure (Set.range (fun i : Fin (N - 1) =>
              ggDepARefl (ggDepAh p N i) (ggDepAα p N i)) ∪
                {ggDepARefl ha1 αa1, ggDepARefl ha2 αa2}), GGDepAIsTv g) ∨
            Out (Set.range (fun i : Fin (N - 1) =>
              ggDepARefl (ggDepAh p N i) (ggDepAα p N i)) ∪
                {ggDepARefl ha1 αa1, ggDepARefl ha2 αa2}))

theorem ggTWDCellsOr_false {p N : ℕ} (h : GGTWDCells p N) : GGTWDCellsOr p N (fun _ => False) := by
  obtain ⟨h1, h2⟩ := h
  unfold GGTWDCellsOr
  refine ⟨?_, ?_⟩
  · intro pos c0 m n hpat ha αa hpairs hdot hx
    exact Or.inl (h1 pos c0 m n hpat ha αa hpairs hdot hx)
  · intro pos c c₂ hpat ha1 αa1 ha2 αa2 hpairs hx
    exact Or.inl (h2 pos c c₂ hpat ha1 αa1 ha2 αa2 hpairs hx)

end CFSG.StandardType

end
