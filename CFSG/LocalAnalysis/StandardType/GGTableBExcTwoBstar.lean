module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoRank

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace TableBExcTwo

theorem eq_zero_or_eq_one_of_card_eq_two {K : Type} [Field K] (hK : Nat.card K = 2) (x : K) :
    x = 0 ∨ x = 1 := by
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (0 : K)).mp hK
  by_cases hx : x = 0
  · exact Or.inl hx
  · right
    rw [hy x hx, hy 1 one_ne_zero]

theorem ringEquiv_apply_eq_of_card_eq_two {K : Type} [Field K] (hK : Nat.card K = 2)
    (σ : K ≃+* K) (x : K) : σ x = x := by
  rcases eq_zero_or_eq_one_of_card_eq_two hK x with rfl | rfl
  · exact map_zero σ
  · exact map_one σ

theorem mem_range_conj_of_mulEquiv {R G : Type*} [Group R] [Group G] (e : R ≃* G)
    (h : ∀ ψ : MulAut G, ψ ∈ (MulAut.conj : G →* MulAut G).range) (φ : MulAut R) :
    φ ∈ (MulAut.conj : R →* MulAut R).range := by
  obtain ⟨g, hg⟩ := h ((e.symm.trans φ).trans e)
  refine ⟨e.symm g, ?_⟩
  ext x
  have h1 := congrArg (fun χ : MulAut G => χ (e x)) hg
  simp only [MulAut.conj_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
  rw [MulAut.conj_apply]
  apply e.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, h1]

theorem ggBstarBound_of_card_le {p r m : ℕ} (hp : 1 < p) {R : Type} [Group R]
    (h : ∀ E : Subgroup (MulAut R), IsElemAbelian p E → Nat.card E ≤ p ^ m) (hrm : m < r + 2)
    (I : Set (MulAut R)) : GGBstarBound p r R I := by
  intro Eb Eh _ _ hr _ _ hEh hcard
  exfalso
  have h1 : p ^ (r + 2) ≤ p ^ m :=
    calc p ^ (r + 2) = p ^ 2 * p ^ r := by ring
      _ ≤ p ^ 2 * Nat.card Eb := Nat.mul_le_mul_left _ hr
      _ ≤ Nat.card Eh := hcard
      _ ≤ p ^ m := h Eh hEh
  have := (Nat.pow_le_pow_iff_right hp).mp h1
  omega

variable
  {τ : Tag} {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem mem_range_conj_adjoint (hτ : τ = .E7 ∨ τ = .E8) (hK : Nat.card K = 2)
    (φ : MulAut (adjointGroup τ K)) :
    φ ∈ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range := by
  obtain ⟨-, Θ, -, -, hker, -⟩ :=
    CFSG.LieType.Chevalley.even_E7_E8_exact_inner_field_automorphism_normal_form (f := 1) le_rfl
      K (by rw [hK]; norm_num) τ hτ
  have h1 : Θ φ = 1 := by
    ext x
    exact (ringEquiv_apply_eq_of_card_eq_two hK _ x).trans rfl
  have h2 : φ ∈ Θ.ker := h1
  rwa [hker] at h2

theorem mem_range_conj_recipe (hτ : τ = .E7 ∨ τ = .E8) (hK : Nat.card K = 2)
    (φ : MulAut (TableBExc.RecipeGroup τ K)) :
    φ ∈ (MulAut.conj : TableBExc.RecipeGroup τ K →* MulAut (TableBExc.RecipeGroup τ K)).range :=
  mem_range_conj_of_mulEquiv (TableBExc.recipeEquiv τ K) (mem_range_conj_adjoint hτ hK) φ

theorem card_le_mulAut_E7 (hK : Nat.card K = 2)
    {E : Subgroup (MulAut (TableBExc.RecipeGroup .E7 K))} (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 3 ^ 7 := by
  have := TableBExc.finite_recipeGroup .E7 K
  obtain ⟨A, hA, hAc⟩ := TableBSymp.exists_of_subset_inn (TableBExc.center_recipeGroup_eq_bot .E7 K)
    (fun φ _ => mem_range_conj_recipe (Or.inl rfl) hK φ) hE
  rw [← hAc]
  exact card_le_recipe_E7 hK hA

theorem card_le_mulAut_E8 (hK : Nat.card K = 2)
    {E : Subgroup (MulAut (TableBExc.RecipeGroup .E8 K))} (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 3 ^ 8 := by
  have := TableBExc.finite_recipeGroup .E8 K
  obtain ⟨A, hA, hAc⟩ := TableBSymp.exists_of_subset_inn (TableBExc.center_recipeGroup_eq_bot .E8 K)
    (fun φ _ => mem_range_conj_recipe (Or.inr rfl) hK φ) hE
  rw [← hAc]
  exact card_le_recipe_E8 hK hA

theorem ggBstarBound_E7Two (hK : Nat.card K = 2) (I : Set (MulAut (TableBExc.RecipeGroup .E7 K))) :
    GGBstarBound 3 6 (TableBExc.RecipeGroup .E7 K) I :=
  ggBstarBound_of_card_le (m := 7) (by norm_num) (fun _ hE => card_le_mulAut_E7 hK hE)
    (by norm_num) I

theorem ggBstarBound_E8Two (hK : Nat.card K = 2) (I : Set (MulAut (TableBExc.RecipeGroup .E8 K))) :
    GGBstarBound 3 7 (TableBExc.RecipeGroup .E8 K) I :=
  ggBstarBound_of_card_le (m := 8) (by norm_num) (fun _ hE => card_le_mulAut_E8 hK hE)
    (by norm_num) I

end TableBExcTwo

end CFSG.StandardType
