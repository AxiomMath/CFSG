module

public import CFSG.LieType.HighestRoot.GenBasic

public section

namespace CFSG.StandardType.LieKnownR2

open CFSG.LieType.HighestRoot CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg

variable {K : Type*} [Group K] (D : UniversalRootDatum K)

theorem exists_pairing_int (hdiv : D.divisible = ∅) {r γ : Fin D.rank → ℤ} (hr : r ∈ D.roots) :
    ∃ c : ℤ, (c : ℚ) * rootForm D r r = 2 * rootForm D γ r := by
  rcases hr with ⟨w, i, hrw⟩ | ⟨w, k, hk, rfl⟩
  · refine ⟨coroot D.cartan i (weylAction D.isFiniteType w⁻¹ γ), ?_⟩
    have h := OfCartan.coroot_mul_form_self D.isFiniteType w i γ
    rw [← hrw] at h
    rw [rootForm, rootForm, form_comm D.isFiniteType (toRat γ) (toRat r)]
    exact h
  · rw [hdiv] at hk
    exact absurd hk (Set.notMem_empty k)

theorem pairing_le_two {r γ : Fin D.rank → ℤ} (hr : IsHighestRoot D r) (hγ : γ ∈ D.roots)
    {c : ℤ} (hc : (c : ℚ) * rootForm D r r = 2 * rootForm D γ r) :
    c ≤ 2 ∧ (c = 2 → γ = r) := by
  have hr0 : toRat r ≠ 0 := fun e =>
    ne_zero_of_mem_roots D.isFiniteType D.divisible hr.mem_roots
      (toRat_injective (by rw [e, map_zero]))
  have hrr : 0 < rootForm D r r := form_pos D.isFiniteType hr0
  have hγγ : rootForm D γ γ ≤ rootForm D r r := hr.longest γ hγ
  have hcs : rootForm D γ r ^ 2 ≤ rootForm D γ γ * rootForm D r r :=
    sq_form_le D.isFiniteType (toRat γ) (toRat r)
  have hsq : rootForm D γ r ^ 2 ≤ rootForm D r r ^ 2 :=
    hcs.trans (by rw [sq]; exact mul_le_mul_of_nonneg_right hγγ hrr.le)
  have hle : rootForm D γ r ≤ rootForm D r r := (abs_le_of_sq_le_sq' hsq hrr.le).2
  have hc2 : (c : ℚ) ≤ 2 := by
    by_contra h
    push Not at h
    nlinarith
  refine ⟨by exact_mod_cast hc2, fun hc2' => ?_⟩
  have hcq : (c : ℚ) = 2 := by exact_mod_cast hc2'
  rw [hcq] at hc
  have heq : rootForm D γ r = rootForm D r r := by linarith
  have h3 := form_sub_self D.isFiniteType γ r
  have h4 : form D.isFiniteType (toRat (γ - r)) (toRat (γ - r)) ≤ 0 := by
    rw [h3]
    change rootForm D γ γ - 2 * rootForm D γ r + rootForm D r r ≤ 0
    linarith
  have h5 : toRat (γ - r) = 0 := by
    by_contra hne
    exact absurd (form_pos D.isFiniteType hne) (not_lt.2 h4)
  exact sub_eq_zero.1 (toRat_injective (by rw [h5, map_zero]))

theorem openCone_subset_of_pos (hdiv : D.divisible = ∅) {r γ δ : Fin D.rank → ℤ}
    (hr : IsHighestRoot D r) (hγ : γ ∈ D.roots) (hδ : δ ∈ D.roots)
    (hγr : 0 < rootForm D γ r) (hδr : 0 < rootForm D δ r) :
    openCone D.roots γ δ ⊆ {r} := by
  rintro ε ⟨hε, a, b, ha, hb, rfl⟩
  have hr0 : toRat r ≠ 0 := fun e =>
    ne_zero_of_mem_roots D.isFiniteType D.divisible hr.mem_roots
      (toRat_injective (by rw [e, map_zero]))
  have hrr : 0 < rootForm D r r := form_pos D.isFiniteType hr0
  obtain ⟨cγ, hcγ⟩ := exists_pairing_int D hdiv (γ := γ) hr.mem_roots
  obtain ⟨cδ, hcδ⟩ := exists_pairing_int D hdiv (γ := δ) hr.mem_roots
  obtain ⟨cε, hcε⟩ := exists_pairing_int D hdiv (γ := a • γ + b • δ) hr.mem_roots
  have hγ1 : 1 ≤ cγ := by
    have : (0 : ℚ) < cγ := by
      by_contra h
      push Not at h
      nlinarith
    exact_mod_cast this
  have hδ1 : 1 ≤ cδ := by
    have : (0 : ℚ) < cδ := by
      by_contra h
      push Not at h
      nlinarith
    exact_mod_cast this
  have hsum : (cε : ℚ) = a * cγ + b * cδ := by
    have h1 : (cε : ℚ) * rootForm D r r = (a * cγ + b * cδ) * rootForm D r r := by
      rw [hcε, rootForm_nsmul_add_nsmul]
      linear_combination (-(a : ℚ)) * hcγ - (b : ℚ) * hcδ
    exact mul_right_cancel₀ hrr.ne' h1
  have hsumZ : cε = a * cγ + b * cδ := by exact_mod_cast hsum
  obtain ⟨hle, heq⟩ := pairing_le_two D hr hε hcε
  have ha1 : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb1 : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have hcε2 : cε = 2 := by nlinarith
  exact heq hcε2

theorem openCone_eq_empty_of_pos (hdiv : D.divisible = ∅) {r γ : Fin D.rank → ℤ}
    (hr : IsHighestRoot D r) (hγ : γ ∈ D.roots) (hγr : 0 < rootForm D γ r) :
    openCone D.roots γ r = ∅ := by
  refine Set.eq_empty_of_forall_notMem ?_
  rintro ε ⟨hε, a, b, ha, hb, rfl⟩
  have hr0 : toRat r ≠ 0 := fun e =>
    ne_zero_of_mem_roots D.isFiniteType D.divisible hr.mem_roots
      (toRat_injective (by rw [e, map_zero]))
  have hrr : 0 < rootForm D r r := form_pos D.isFiniteType hr0
  obtain ⟨cγ, hcγ⟩ := exists_pairing_int D hdiv (γ := γ) hr.mem_roots
  obtain ⟨cε, hcε⟩ := exists_pairing_int D hdiv (γ := a • γ + b • r) hr.mem_roots
  have hγ1 : 1 ≤ cγ := by
    have : (0 : ℚ) < cγ := by
      by_contra h
      push Not at h
      nlinarith
    exact_mod_cast this
  have hsum : (cε : ℚ) = a * cγ + b * 2 := by
    have h1 : (cε : ℚ) * rootForm D r r = (a * cγ + b * 2) * rootForm D r r := by
      rw [hcε, rootForm_nsmul_add_nsmul]
      linear_combination (-(a : ℚ)) * hcγ
    exact mul_right_cancel₀ hrr.ne' h1
  have hsumZ : cε = a * cγ + b * 2 := by exact_mod_cast hsum
  have ha1 : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb1 : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have hle := (pairing_le_two D hr hε hcε).1
  nlinarith

end CFSG.StandardType.LieKnownR2
