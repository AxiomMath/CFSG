module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma212Aux

public section

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.RegFam

variable {G : Type*} [Group G]

@[expose] def conjOrbit (L F : Subgroup G) : Set (Subgroup G) :=
  {K | ∃ f ∈ F, K = L.map (MulAut.conj f).toMonoidHom}

theorem mem_conjOrbit {L F K : Subgroup G} :
    K ∈ conjOrbit L F ↔ ∃ f ∈ F, K = L.map (MulAut.conj f).toMonoidHom := Iff.rfl

theorem self_mem_conjOrbit (L F : Subgroup G) : L ∈ conjOrbit L F :=
  ⟨1, one_mem F, (Near.Thm210.map_conj_one L).symm⟩

theorem conjOrbit_eq_of_mem {L F K : Subgroup G} (hK : K ∈ conjOrbit L F) :
    conjOrbit K F = conjOrbit L F := by
  obtain ⟨f, hf, rfl⟩ := hK
  ext K'
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g * f, mul_mem hg hf, by rw [Near.Thm210.map_conj_map_conj]⟩
  · rintro ⟨g, hg, rfl⟩
    refine ⟨g * f⁻¹, mul_mem hg (inv_mem hf), ?_⟩
    rw [Near.Thm210.map_conj_map_conj, mul_assoc, inv_mul_cancel, mul_one]

theorem conjOrbit_eq_or_disjoint (L L' F : Subgroup G) :
    conjOrbit L F = conjOrbit L' F ∨ Disjoint (conjOrbit L F) (conjOrbit L' F) := by
  by_cases h : ∃ K, K ∈ conjOrbit L F ∧ K ∈ conjOrbit L' F
  · obtain ⟨K, hK, hK'⟩ := h
    exact Or.inl ((conjOrbit_eq_of_mem hK).symm.trans (conjOrbit_eq_of_mem hK'))
  · refine Or.inr (Set.disjoint_left.mpr fun K hK hK' => h ⟨K, hK, hK'⟩)

theorem orbitClosure_eq_sSup_conjOrbit (L F : Subgroup G) :
    orbitClosure L F = sSup (conjOrbit L F) :=
  Near.Lemma212.orbitClosure_eq_sSup L F

theorem conjOrbit_subset {Ω : Set (Subgroup G)} {L F : Subgroup G} (hL : L ∈ Ω)
    (hF : ∀ f ∈ F, ∀ J ∈ Ω, J.map (MulAut.conj f).toMonoidHom ∈ Ω) : conjOrbit L F ⊆ Ω := by
  rintro _ ⟨f, hf, rfl⟩
  exact hF f hf L hL

theorem conjOrbit_disjoint_of_not_mem {L L' F : Subgroup G} (h : L' ∉ conjOrbit L F) :
    Disjoint (conjOrbit L F) (conjOrbit L' F) := by
  rcases conjOrbit_eq_or_disjoint L L' F with h1 | h1
  · exact absurd (h1 ▸ self_mem_conjOrbit L' F) h
  · exact h1

variable {Ω : Set (Subgroup G)} {H F : Subgroup G}

theorem disjoint_orbitClosure [Finite G] (hΩ : IsDirectProduct Ω H)
    (hF : ∀ f ∈ F, ∀ J ∈ Ω, J.map (MulAut.conj f).toMonoidHom ∈ Ω) {L L' : Subgroup G}
    (hL : L ∈ Ω) (hL' : L' ∈ Ω) (h : L' ∉ conjOrbit L F) :
    Disjoint (orbitClosure L F) (orbitClosure L' F) := by
  rw [orbitClosure_eq_sSup_conjOrbit, orbitClosure_eq_sSup_conjOrbit]
  exact Near.Thm210.disjoint_sSup_sSup hΩ (conjOrbit_subset hL hF) (conjOrbit_subset hL' hF)
    (conjOrbit_disjoint_of_not_mem h)

theorem commute_orbitClosure (hΩ : IsDirectProduct Ω H)
    (hF : ∀ f ∈ F, ∀ J ∈ Ω, J.map (MulAut.conj f).toMonoidHom ∈ Ω) {L L' : Subgroup G}
    (hL : L ∈ Ω) (hL' : L' ∈ Ω) (h : L' ∉ conjOrbit L F) :
    ∀ x ∈ orbitClosure L F, ∀ y ∈ orbitClosure L' F, Commute x y := by
  rw [orbitClosure_eq_sSup_conjOrbit, orbitClosure_eq_sSup_conjOrbit]
  exact Near.Lemma212.commute_sSup_sSup hΩ (conjOrbit_disjoint_of_not_mem h)
    (conjOrbit_subset hL hF) (conjOrbit_subset hL' hF)

theorem isDirectProduct_orbitClosure [Finite G] (hΩ : IsDirectProduct Ω H)
    (hF : ∀ f ∈ F, ∀ J ∈ Ω, J.map (MulAut.conj f).toMonoidHom ∈ Ω) :
    IsDirectProduct {U | ∃ L ∈ Ω, U = orbitClosure L F} H where
  commute := by
    rintro _ ⟨L, hL, rfl⟩ _ ⟨L', hL', rfl⟩ hne
    refine commute_orbitClosure hΩ hF hL hL' fun hmem => hne ?_
    rw [orbitClosure_eq_sSup_conjOrbit, orbitClosure_eq_sSup_conjOrbit,
      conjOrbit_eq_of_mem hmem]
  indep := by
    rintro _ ⟨L, hL, rfl⟩
    have hle : sSup ({U | ∃ L ∈ Ω, U = orbitClosure L F} \ {orbitClosure L F}) ≤
        sSup (Ω \ conjOrbit L F) := by
      refine sSup_le ?_
      rintro _ ⟨⟨L', hL', rfl⟩, hne⟩
      have hmem : L' ∉ conjOrbit L F := fun hmem => hne (by
        rw [Set.mem_singleton_iff, orbitClosure_eq_sSup_conjOrbit,
          orbitClosure_eq_sSup_conjOrbit, conjOrbit_eq_of_mem hmem])
      rw [orbitClosure_eq_sSup_conjOrbit]
      refine sSup_le_sSup fun K hK => ⟨conjOrbit_subset hL' hF hK, fun hKL => ?_⟩
      exact Set.disjoint_left.mp (conjOrbit_disjoint_of_not_mem hmem) hKL hK
    refine Disjoint.mono_right hle ?_
    rw [orbitClosure_eq_sSup_conjOrbit]
    exact Near.Thm210.disjoint_sSup_sSup hΩ (conjOrbit_subset hL hF) Set.sdiff_subset
      Set.disjoint_sdiff_right
  sSup_eq := by
    refine le_antisymm (sSup_le ?_) ?_
    · rintro _ ⟨L, hL, rfl⟩
      exact orbitClosure_le fun f hf => hΩ.le (hF f hf L hL)
    · rw [← hΩ.sSup_eq]
      refine sSup_le fun J hJ => ?_
      exact (le_orbitClosure J F).trans (le_sSup ⟨J, hJ, rfl⟩)

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.RegFam
