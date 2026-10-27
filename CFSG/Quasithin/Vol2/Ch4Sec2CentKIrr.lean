module

public import CFSG.Quasithin.Background.C3Defs

public section

namespace CFSG.Quasithin.H13.Ch4.CentK

open CFSG.Assembly.LowTwoRank Matrix CFSG.Quasithin

variable {G : Type} [Group G]

private theorem exists_statedSL_two_of_det {F : Type} [Field F] (M : Matrix (Fin 2) (Fin 2) F)
    (hM : M.det = 1) :
    ∃ s : ↥(StatedSL 2 F), ((s : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = M :=
  ⟨specialLinearGroupEquivStatedSL 2 F ⟨M, hM⟩, specialLinearGroupEquivStatedSL_coe 2 F ⟨M, hM⟩⟩

private theorem all_of_closed_two {F : Type} [Field F] (hF : (2 : F) = 0)
    (P : (Fin 2 → F) → Prop) (hadd : ∀ x y, P x → P y → P (x + y))
    (hclosed : ∀ M : Matrix (Fin 2) (Fin 2) F, M.det = 1 → ∀ x, P x → P (M *ᵥ x))
    {ω : Fin 2 → F} (hω : P ω) (hω0 : ω ≠ 0) : ∀ y, P y := by
  have htau : ∀ a : F, ∀ x, P x → P ![x 0 + a * x 1, x 1] := by
    intro a x hx
    have h1 := hclosed !![1, a; 0, 1] (by rw [Matrix.det_fin_two_of]; ring) x hx
    have h2 : (!![1, a; 0, 1] : Matrix (Fin 2) (Fin 2) F) *ᵥ x = ![x 0 + a * x 1, x 1] := by
      funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rwa [h2] at h1
  have hsig : ∀ x, P x → P ![x 1, x 0] := by
    intro x hx
    have h1 := hclosed !![0, 1; 1, 0]
      (by rw [Matrix.det_fin_two_of]; linear_combination -hF) x hx
    have h2 : (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) *ᵥ x = ![x 1, x 0] := by
      funext i
      fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rwa [h2] at h1
  have key : ∀ x, P x → x 1 ≠ 0 → ∀ c d : F, P ![c, d] := by
    intro x hx hx1
    have hinv : (x 1)⁻¹ * x 1 = 1 := inv_mul_cancel₀ hx1
    have hc : ∀ c : F, P ![c, 0] := by
      intro c
      have h := hadd x _ hx (htau (c * (x 1)⁻¹) x hx)
      have e : x + ![x 0 + c * (x 1)⁻¹ * x 1, x 1] = ![c, 0] := by
        funext i
        fin_cases i
        · show x 0 + (x 0 + c * (x 1)⁻¹ * x 1) = c
          linear_combination x 0 * hF + c * hinv
        · show x 1 + x 1 = 0
          linear_combination x 1 * hF
      rwa [e] at h
    have hd : ∀ d : F, P ![0, d] := fun d => by simpa using hsig _ (hc d)
    intro c d
    have h := hadd _ _ (hc c) (hd d)
    have e2 : ![c, 0] + ![0, d] = ![c, d] := by
      funext i
      fin_cases i <;> simp
    rwa [e2] at h
  have hall : ∀ c d : F, P ![c, d] := by
    by_cases h1 : ω 1 = 0
    · have h0 : ω 0 ≠ 0 := by
        intro h0
        apply hω0
        funext i
        fin_cases i <;> simp [h0, h1]
      exact key _ (hsig ω hω) (by simpa using h0)
    · exact key ω hω h1
  intro y
  have e : y = ![y 0, y 1] := by
    funext i
    fin_cases i <;> rfl
  rw [e]
  exact hall _ _

private theorem le_of_natural_aux {A V₁ V₂ : Subgroup G} {N : Subgroup ↥A} {F : Type} [Field F]
    (hF : (2 : F) = 0) (h₁ : IsNaturalSection A V₁ ⊥ N (StatedSL 2 F))
    (h₂ : IsNaturalSection A V₂ ⊥ N (StatedSL 2 F)) (hne : V₁ ⊓ V₂ ≠ ⊥) : V₁ ≤ V₂ := by
  obtain ⟨hA₁, α, hα, -, β, -, hβker, hβ⟩ := h₁
  obtain ⟨hA₂, -⟩ := h₂
  have hinj : ∀ x y : ↥V₁, β x = β y → (x : G) = y := by
    intro x y hxy
    have h1 : x * y⁻¹ ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
    rw [hβker, Subgroup.mem_subgroupOf, Subgroup.mem_bot, Subgroup.coe_mul, Subgroup.coe_inv,
      mul_inv_eq_one] at h1
    exact h1
  have hadd : ∀ x y : Fin 2 → F,
      (∃ u : ↥V₁, (u : G) ∈ V₂ ∧ Multiplicative.toAdd (β u) = x) →
      (∃ u : ↥V₁, (u : G) ∈ V₂ ∧ Multiplicative.toAdd (β u) = y) →
      ∃ u : ↥V₁, (u : G) ∈ V₂ ∧ Multiplicative.toAdd (β u) = x + y := by
    rintro x y ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
    exact ⟨u * u', V₂.mul_mem hu hu', by rw [map_mul, toAdd_mul]⟩
  have hclosed : ∀ M : Matrix (Fin 2) (Fin 2) F, M.det = 1 → ∀ x : Fin 2 → F,
      (∃ u : ↥V₁, (u : G) ∈ V₂ ∧ Multiplicative.toAdd (β u) = x) →
      ∃ u : ↥V₁, (u : G) ∈ V₂ ∧ Multiplicative.toAdd (β u) = M *ᵥ x := by
    rintro M hM x ⟨u, hu, rfl⟩
    obtain ⟨s, hs⟩ := exists_statedSL_two_of_det M hM
    obtain ⟨a, ha⟩ := hα s
    have hmem : (a : G) * (u : G) * (a : G)⁻¹ ∈ V₁ :=
      (Subgroup.mem_set_normalizer_iff.mp (hA₁ a.2) (u : G)).mp u.2
    have hmem₂ : (a : G) * (u : G) * (a : G)⁻¹ ∈ V₂ :=
      (Subgroup.mem_set_normalizer_iff.mp (hA₂ a.2) (u : G)).mp hu
    have hcompat := hβ a u ⟨(a : G) * (u : G) * (a : G)⁻¹, hmem⟩ rfl
    rw [ha, hs] at hcompat
    exact ⟨⟨_, hmem⟩, hmem₂, hcompat⟩
  obtain ⟨w, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  obtain ⟨hwV₁, hwV₂⟩ := Subgroup.mem_inf.mp w.2
  have hω : ∃ u : ↥V₁, (u : G) ∈ V₂ ∧
      Multiplicative.toAdd (β u) = Multiplicative.toAdd (β ⟨(w : G), hwV₁⟩) :=
    ⟨⟨(w : G), hwV₁⟩, hwV₂, rfl⟩
  have hω0 : Multiplicative.toAdd (β ⟨(w : G), hwV₁⟩) ≠ 0 := by
    intro h0
    have hβ1 : β ⟨(w : G), hwV₁⟩ = β 1 := by
      rw [map_one]
      exact Multiplicative.toAdd.injective (h0.trans toAdd_one.symm)
    exact hw1 (Subtype.ext (hinj _ _ hβ1))
  have hall := all_of_closed_two hF (fun x => ∃ u : ↥V₁, (u : G) ∈ V₂ ∧
      Multiplicative.toAdd (β u) = x) hadd hclosed (ω := Multiplicative.toAdd (β ⟨(w : G), hwV₁⟩))
    hω hω0
  intro g hg
  obtain ⟨u, hu₂, hu⟩ := hall (Multiplicative.toAdd (β ⟨g, hg⟩))
  have h1 : (u : G) = g := hinj u ⟨g, hg⟩ (Multiplicative.toAdd.injective hu)
  rw [← h1]
  exact hu₂

theorem eq_of_inf_ne_bot_of_natural {A V₁ V₂ : Subgroup G} {N : Subgroup ↥A} {F : Type}
    [Field F] [Fintype F] (hF : (2 : F) = 0) (h₁ : IsNaturalSection A V₁ ⊥ N (StatedSL 2 F))
    (h₂ : IsNaturalSection A V₂ ⊥ N (StatedSL 2 F)) (hne : V₁ ⊓ V₂ ≠ ⊥) : V₁ = V₂ := by
  refine le_antisymm (le_of_natural_aux hF h₁ h₂ hne) (le_of_natural_aux hF h₂ h₁ ?_)
  rwa [inf_comm]

end CFSG.Quasithin.H13.Ch4.CentK
