module

public import CFSG.RankThree.GF2n.Smith81.S81VGeomA
public import CFSG.RankThree.GF2n.Smith81.S81VGeomE1
public import CFSG.RankThree.GF2n.Smith81.S81VGeomE2

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module

variable {F : Type} [Field F] {σ : F ≃+* F}

theorem lemmaE_caseI [Finite F] [CharP F 2] (hσ : IsUnitaryInvolution σ)
    (hq : 3 ≤ Nat.card (Fσ σ)) {S : Set (Fin 6 → F)} (hS : ClosedPts σ S)
    {P4 P3 P2 : Submodule F (Fin 6 → F)} (h4 : finrank F P4 = 4) (h3 : finrank F P3 = 3)
    (h2 : finrank F P2 = 2) (h32 : P3 ≤ P4) (hn3 : NonDeg σ P3) (hn2 : NonDeg σ P2)
    {p₄ : Fin 6 → F} (hp4S : p₄ ∈ S) (hp4P : p₄ ∈ P4) (hp4P3 : p₄ ∉ P3)
    (hperp : P3 ⊓ orth σ (Submodule.span F {p₄}) = P2)
    (hE0 : ∀ z ∈ P3, z ≠ 0 → herm σ z z = 0 → z ∈ S)
    {p : Fin 6 → F} (hpP : p ∈ P4) (hp0 : p ≠ 0) (hpi : herm σ p p = 0) (hpP3 : p ∉ P3)
    (hj : herm σ p p₄ ≠ 0) : p ∈ S := by
  have hp4i : herm σ p₄ p₄ = 0 := (hS.iso p₄ hp4S).2
  have hsup : P3 ⊔ Submodule.span F {p₄} = P4 :=
    Submodule.eq_of_le_of_finrank_eq
      (sup_le h32 (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hp4P)))
      (by have := Submodule.finrank_sup_span_singleton hp4P3; omega)
  have hpP' : p ∈ P3 ⊔ Submodule.span F {p₄} := by rw [hsup]; exact hpP
  obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.mp hpP'
  obtain ⟨γ, rfl⟩ := Submodule.mem_span_singleton.mp hw
  have hpeq : p = u + γ • p₄ := huw.symm
  have hj' : herm σ u p₄ ≠ 0 := by
    rw [hpeq, herm_add_left, herm_smul_left, hp4i, mul_zero, add_zero] at hj
    exact hj
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hj' (herm_zero_left σ p₄)
  by_cases hui : herm σ u u = 0
  ·
    have huS : u ∈ S := hE0 u hu hu0 hui
    refine hS.secant u huS p₄ hp4S hj' p hp0 hpi ?_
    rw [hpeq]
    exact Submodule.mem_span_pair.mpr ⟨1, γ, by simp⟩
  ·
    obtain ⟨L, r, hLP3, huL, hL2, hLnd, -, hr2, hr3, hr1⟩ :=
      exists_good_line hσ hq h3 h2 hn3 hn2 hperp hu hui hj'
    have hWnd : NonDeg σ (L ⊔ Submodule.span F {p₄}) :=
      nonDeg_sup_span hσ.invol hp4i hr1 hr2 hr3 huL hj'
    have hp4L : p₄ ∉ L := fun h => hp4P3 (hLP3 h)
    have hW3 : finrank F ↥(L ⊔ Submodule.span F {p₄}) = 3 := by
      have := Submodule.finrank_sup_span_singleton hp4L
      omega
    obtain ⟨c₁, hc₁L, c₂, hc₂L, hc₁i, hc₂i, hc₁c₂⟩ := exists_isotropic_pair hσ hL2 hLnd
    have hc₁0 : c₁ ≠ 0 := by
      rintro rfl
      exact hc₁c₂ (herm_zero_left σ c₂)
    have hc₂0 : c₂ ≠ 0 := by
      rintro rfl
      exact hc₁c₂ (herm_zero_right σ c₁)
    have hc₁S : c₁ ∈ S := hE0 c₁ (hLP3 hc₁L) hc₁0 hc₁i
    have hc₂S : c₂ ∈ S := hE0 c₂ (hLP3 hc₂L) hc₂0 hc₂i
    have hc₁W : c₁ ∈ L ⊔ Submodule.span F {p₄} := Submodule.mem_sup_left hc₁L
    have hc₂W : c₂ ∈ L ⊔ Submodule.span F {p₄} := Submodule.mem_sup_left hc₂L
    have hp4W : p₄ ∈ L ⊔ Submodule.span F {p₄} :=
      Submodule.mem_sup_right (Submodule.mem_span_singleton_self p₄)
    have hpW : p ∈ L ⊔ Submodule.span F {p₄} := by
      rw [hpeq]
      exact Submodule.add_mem_sup huL
        (Submodule.smul_mem _ γ (Submodule.mem_span_singleton_self p₄))
    have hind : LinearIndependent F ![c₁, c₂, p₄] := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      have hg' : g 0 • c₁ + g 1 • c₂ + g 2 • p₄ = 0 := by
        simpa [Fin.sum_univ_three] using hg
      have hg2 : g 2 = 0 := by
        by_contra hne
        have h1 : g 2 • p₄ = -(g 0 • c₁ + g 1 • c₂) := eq_neg_of_add_eq_zero_right hg'
        have hmem : (g 2)⁻¹ • -(g 0 • c₁ + g 1 • c₂) ∈ P3 :=
          P3.smul_mem _ (P3.neg_mem (P3.add_mem (P3.smul_mem _ (hLP3 hc₁L))
            (P3.smul_mem _ (hLP3 hc₂L))))
        rw [← h1, smul_smul, inv_mul_cancel₀ hne, one_smul] at hmem
        exact hp4P3 hmem
      rw [hg2, zero_smul, add_zero] at hg'
      have hg1 : g 1 = 0 := by
        have h := congrArg (herm σ c₁) hg'
        simp only [herm_add_right, herm_smul_right, hc₁i, mul_zero, zero_add,
          herm_zero_right] at h
        exact (mul_eq_zero.1 h).resolve_right hc₁c₂
      rw [hg1, zero_smul, add_zero] at hg'
      have hg0 : g 0 = 0 := (smul_eq_zero.1 hg').resolve_right hc₁0
      intro i
      fin_cases i <;> simp [hg0, hg1, hg2]
    exact lemmaA hσ hWnd hW3 hS hc₁S hc₂S hp4S hc₁W hc₂W hp4W hind p hpW hp0 hpi

end CFSG.RankThree.GF2n.Smith81.S81V
