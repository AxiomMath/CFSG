module

public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoRank
public import CFSG.LocalAnalysis.StandardType.GGTableBF4Bstar

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace TableBF4Two

theorem eq_zero_of_three_nsmul {x : ZMod (2 * 1)} (h : 3 • x = 0) : x = 0 := by
  revert x
  decide

variable
  {K : Type} [Field K] [Finite K] [CharP K 2]

theorem mem_range_conj_of_pow_three (hK : Nat.card K = 2)
    {φ : MulAut (adjointGroup .F4 K)} (hφ : φ ^ 3 = 1) :
    φ ∈ (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range := by
  have : CharP K CFSG.LieType.Ree.ReeTag.F4.prime := ‹CharP K 2›
  obtain ⟨-, -, ⟨Θ₀, -, -, hker₀⟩, -⟩ :=
    even_F4_exact_automorphism_normal_form (f := 1) le_rfl K (by rw [hK]; norm_num)
  obtain ⟨Θ, hker⟩ : ∃ Θ : MulAut (adjointGroup .F4 K) →* Multiplicative (ZMod (2 * 1)),
      Θ.ker = (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range :=
    ⟨Θ₀, hker₀⟩
  have h1 : Θ φ ^ 3 = 1 := by rw [← map_pow, hφ, map_one]
  have h2 : 3 • Multiplicative.toAdd (Θ φ) = 0 := by
    rw [← toAdd_pow, h1, toAdd_one]
  have h4 : Θ φ = 1 := by
    rw [← ofAdd_toAdd (Θ φ), eq_zero_of_three_nsmul h2, ofAdd_zero]
  have h5 : φ ∈ Θ.ker := h4
  rw [hker] at h5
  exact h5

theorem mem_range_conj_recipe (hK : Nat.card K = 2) {φ : MulAut (TableBF4.RecipeGroup K)}
    (hφ : φ ^ 3 = 1) :
    φ ∈ (MulAut.conj : TableBF4.RecipeGroup K →* MulAut (TableBF4.RecipeGroup K)).range := by
  set e := TableBF4.recipeEquiv K
  set ψ : MulAut (adjointGroup .F4 K) := (e.symm.trans φ).trans e with hψ
  have hψφ : ∀ k : ℕ, ∀ g, (ψ ^ k) g = e ((φ ^ k) (e.symm g)) := by
    intro k
    induction k with
    | zero => intro g; simp
    | succ k ih =>
      intro g
      rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, ih]
      simp [hψ]
  have hψ3 : ψ ^ 3 = 1 := by
    ext g
    rw [hψφ, hφ, MulAut.one_apply, MulAut.one_apply, MulEquiv.apply_symm_apply]
  obtain ⟨g, hg⟩ := mem_range_conj_of_pow_three hK hψ3
  refine ⟨e.symm g, ?_⟩
  ext x
  have h1 := congrArg (fun χ : MulAut (adjointGroup .F4 K) => χ (e x)) hg
  simp only [MulAut.conj_apply, hψ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
  rw [MulAut.conj_apply]
  apply e.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, h1]

theorem card_le_mulAut (hK : Nat.card K = 2) {E : Subgroup (MulAut (TableBF4.RecipeGroup K))}
    (hE : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ 4 := by
  have := TableBF4.finite_recipeGroup (K := K)
  have hEI : (E : Set (MulAut (TableBF4.RecipeGroup K))) ⊆
      Set.range (MulAut.conj : TableBF4.RecipeGroup K →* _) := fun φ hφ =>
    mem_range_conj_recipe hK (hE.2 φ hφ)
  obtain ⟨A, hA, hAc⟩ := TableBSymp.exists_of_subset_inn (TableBF4.center_recipeGroup_eq_bot K)
    hEI hE
  rw [← hAc]
  exact card_le_recipeGroup hK hA

theorem ggBstarBound_F4Two (hK : Nat.card K = 2) (r : ℕ)
    (I : Set (MulAut (TableBF4.RecipeGroup K))) : GGBstarBound 3 r (TableBF4.RecipeGroup K) I := by
  intro Eb Eh _ _ _ h3 _ hEh hcard
  exfalso
  have h1 := card_le_mulAut hK hEh
  have h2 : 3 ^ 5 ≤ 3 ^ 4 :=
    calc 3 ^ 5 = 3 ^ 2 * 3 ^ 3 := by norm_num
      _ ≤ 3 ^ 2 * Nat.card Eb := Nat.mul_le_mul_left _ h3
      _ ≤ Nat.card Eh := hcard
      _ ≤ 3 ^ 4 := h1
  norm_num at h2

end TableBF4Two

end CFSG.StandardType
