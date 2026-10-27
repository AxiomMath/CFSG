module

public import CFSG.ClassicalGroups.Unitary.Form
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.SU4TotSingFq

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.ClassicalGroups.Unitary

variable {F : Type} [Field F] [Finite F] {σ : F ≃+* F} {n : ℕ}

theorem herm_mem_fixedField (hσ : IsUnitaryInvolution σ) (h2 : (2 : F) = 0)
    (E : AddSubgroup (Fin 4 → F)) (hQ : ∀ x ∈ E, herm σ x x = 0) {x y : Fin 4 → F}
    (hx : x ∈ E) (hy : y ∈ E) : σ (herm σ x y) = herm σ x y := by
  have hxy : herm σ (x + y) (x + y) = 0 := hQ (x + y) (E.add_mem hx hy)
  rw [herm_add_left, herm_add_right, herm_add_right] at hxy
  simp only [hQ x hx, hQ y hy, zero_add, add_zero] at hxy
  rw [herm_conj σ hσ.invol x y] at hxy
  have hσt : σ (herm σ x y) = -herm σ x y := eq_neg_of_add_eq_zero_right hxy
  have h2t : herm σ x y + herm σ x y = 0 := by rw [← two_mul, h2, zero_mul]
  have ht : -herm σ x y = herm σ x y := neg_eq_of_add_eq_zero_left h2t
  rw [hσt, ht]

private theorem closure_eq_of_herm_fixed_T1J2 (hσ : IsUnitaryInvolution σ) (h2 : (2 : F) = 0)
    (hF : Nat.card F = (2 ^ n) ^ 2) (E : AddSubgroup (Fin 4 → F))
    (hE : Nat.card E = 2 ^ (4 * n)) (S : Set (Fin 4 → F))
    (hSE : (E : Set (Fin 4 → F)) ⊆ S)
    (hS : ∀ x ∈ S, ∀ y ∈ S, σ (herm σ x y) = herm σ x y) :
    AddSubgroup.closure S = E := by
  have hcard : Nat.card (AddSubgroup.closure S) ≤ 2 ^ (4 * n) :=
    card_closure_le_of_herm_fixed hσ h2 hF S hS
  have hle : E ≤ AddSubgroup.closure S := fun a ha => AddSubgroup.subset_closure (hSE ha)
  have hcard' : Nat.card (AddSubgroup.closure S) ≤ Nat.card E := by rwa [hE]
  exact (AddSubgroup.eq_of_le_of_card_ge hle hcard').symm

theorem smul_mem_of_totSing (hσ : IsUnitaryInvolution σ) (h2 : (2 : F) = 0)
    (hF : Nat.card F = (2 ^ n) ^ 2) (E : AddSubgroup (Fin 4 → F))
    (hE : Nat.card E = 2 ^ (4 * n)) (hQ : ∀ x ∈ E, herm σ x x = 0) {c : F} (hc : σ c = c)
    {x : Fin 4 → F} (hx : x ∈ E) : c • x ∈ E := by
  have hSE : (E : Set (Fin 4 → F)) ⊆ (E : Set (Fin 4 → F)) ∪ {c • x} := fun a ha => Or.inl ha
  have hS : ∀ a ∈ (E : Set (Fin 4 → F)) ∪ {c • x},
      ∀ b ∈ (E : Set (Fin 4 → F)) ∪ {c • x}, σ (herm σ a b) = herm σ a b := by
    intro a ha b hb
    simp only [Set.mem_union, Set.mem_singleton_iff] at ha hb
    rcases ha with haE | rfl
    · rcases hb with hbE | rfl
      · exact herm_mem_fixedField hσ h2 E hQ haE hbE
      · rw [herm_smul_right, map_mul, hc, herm_mem_fixedField hσ h2 E hQ haE hx]
    · rcases hb with hbE | rfl
      · rw [herm_smul_left, map_mul, hσ.invol c, hc, herm_mem_fixedField hσ h2 E hQ hx hbE]
      · simp [hQ x hx]
  have hcl := closure_eq_of_herm_fixed_T1J2 hσ h2 hF E hE
    ((E : Set (Fin 4 → F)) ∪ {c • x}) hSE hS
  have hmem : c • x ∈ AddSubgroup.closure ((E : Set (Fin 4 → F)) ∪ {c • x}) :=
    AddSubgroup.subset_closure (Or.inr (Set.mem_singleton _))
  rw [hcl] at hmem
  exact hmem

private theorem exists_line_of_herm_eq_zero_T1J2 (hσ : IsUnitaryInvolution σ) (h2 : (2 : F) = 0)
    (hF : Nat.card F = (2 ^ n) ^ 2) (E : AddSubgroup (Fin 4 → F))
    (hE : Nat.card E = 2 ^ (4 * n)) (hQ : ∀ x ∈ E, herm σ x x = 0)
    (hzero : ∀ x ∈ E, ∀ y ∈ E, herm σ x y = 0) :
    ∃ v : Fin 4 → F, v ≠ 0 ∧ herm σ v v = 0 ∧ ∀ c : F, c • v ∈ E := by
  have hcardF : 1 < Nat.card F := by
    haveI : Fintype F := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    rw [hn0] at hF
    simp at hF
    omega
  have hEcard : 1 < Nat.card E := by
    rw [hE]
    exact Nat.one_lt_pow (by omega) (by norm_num)
  have hEne : E ≠ ⊥ := (AddSubgroup.one_lt_card_iff_ne_bot E).1 hEcard
  haveI : Nontrivial E := (AddSubgroup.nontrivial_iff_ne_bot E).2 hEne
  obtain ⟨v, hvE, hv0⟩ := AddSubgroup.exists_ne_zero_of_nontrivial E
  refine ⟨v, hv0, hQ v hvE, ?_⟩
  intro c
  have hSE : (E : Set (Fin 4 → F)) ⊆
      (E : Set (Fin 4 → F)) ∪ Set.range (fun d : F => d • v) := fun a ha => Or.inl ha
  have hS : ∀ a ∈ (E : Set (Fin 4 → F)) ∪ Set.range (fun d : F => d • v),
      ∀ b ∈ (E : Set (Fin 4 → F)) ∪ Set.range (fun d : F => d • v),
        σ (herm σ a b) = herm σ a b := by
    intro a ha b hb
    simp only [Set.mem_union] at ha hb
    rcases ha with haE | ⟨ca, rfl⟩
    · rcases hb with hbE | ⟨cb, rfl⟩
      · simp [hzero a haE b hbE]
      · simp [hzero a haE v hvE]
    · rcases hb with hbE | ⟨cb, rfl⟩
      · simp [hzero v hvE b hbE]
      · simp [hQ v hvE]
  have hcl := closure_eq_of_herm_fixed_T1J2 hσ h2 hF E hE
    ((E : Set (Fin 4 → F)) ∪ Set.range (fun d : F => d • v)) hSE hS
  have hmem : c • v ∈
      AddSubgroup.closure ((E : Set (Fin 4 → F)) ∪ Set.range (fun d : F => d • v)) :=
    AddSubgroup.subset_closure (Or.inr ⟨c, rfl⟩)
  rw [hcl] at hmem
  exact hmem

theorem exists_isotropic_line_or_hyperbolic_pair (hσ : IsUnitaryInvolution σ) (h2 : (2 : F) = 0)
    (hF : Nat.card F = (2 ^ n) ^ 2) (E : AddSubgroup (Fin 4 → F))
    (hE : Nat.card E = 2 ^ (4 * n)) (hQ : ∀ x ∈ E, herm σ x x = 0) :
    (∃ v : Fin 4 → F, v ≠ 0 ∧ herm σ v v = 0 ∧ ∀ c : F, c • v ∈ E) ∨
      ∃ e ∈ E, ∃ f ∈ E, herm σ e f = 1 := by
  by_cases hzero : ∀ x ∈ E, ∀ y ∈ E, herm σ x y = 0
  · exact Or.inl (exists_line_of_herm_eq_zero_T1J2 hσ h2 hF E hE hQ hzero)
  · right
    push Not at hzero
    obtain ⟨x, hxE, y, hyE, hxy⟩ := hzero
    have hfix : σ (herm σ x y) = herm σ x y := herm_mem_fixedField hσ h2 E hQ hxE hyE
    have hinv : σ (herm σ x y)⁻¹ = (herm σ x y)⁻¹ := by rw [map_inv₀, hfix]
    have hfE : (herm σ x y)⁻¹ • y ∈ E := smul_mem_of_totSing hσ h2 hF E hE hQ hinv hyE
    exact ⟨x, hxE, (herm σ x y)⁻¹ • y, hfE,
      by rw [herm_smul_right, inv_mul_cancel₀ hxy]⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
