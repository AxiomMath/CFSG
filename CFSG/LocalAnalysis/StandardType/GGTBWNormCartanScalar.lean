module

public import CFSG.LinearAlgebra.Reflection.Generated
public import CFSG.LocalAnalysis.StandardType.GGFLWTree
public import CFSG.LocalAnalysis.StandardType.GGFLWReflForm

public noncomputable section
open scoped BigOperators
namespace CFSG.StandardType
open CFSG CFSG.Assembly
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem scalar_sq_eq_one_of_cartan_reflection_datum
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : CoxeterMatrix ι) (hM : GGIsWeylMatrix M)
    (C : Matrix ι ι ℤ) (hC : GGIntCartan M C)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : ι → V) (α : ι → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p))
    (σ : ι → V ≃ₗ[ZMod p] V) (hσ : ∀ i v, σ i v = v - α i v • h i)
    (s : V ≃ₗ[ZMod p] V) (hs : s ∈ Subgroup.closure (Set.range σ))
    (c : ZMod p) (hsc : ∀ v, s v = c • v) : c ^ 2 = 1 := by
  classical
  by_cases hc : c = 1
  · rw [hc, one_pow]
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp hz
    have hl := Nat.le_of_dvd (by norm_num : 0 < 2) hd
    omega
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro hz
    have hd : p ∣ 3 := (CharP.cast_eq_zero_iff (ZMod p) p 3).mp hz
    have hl := Nat.le_of_dvd (by norm_num : 0 < 3) hd
    omega
  obtain ⟨D, hTree, hbond⟩ := ggFLW_cartanTree_bonds hM
  have hP : ∀ i j, i ≠ j → (α i (h j) ≠ 0 ↔ D i j ≠ 0) := by
    intro i j hij
    rw [hbond i j hij]
    rcases hC.entries hij with ⟨hm, h0, -⟩ | ⟨hm, h1, -⟩ |
      ⟨hm, ⟨h1, -⟩ | ⟨h2', -⟩⟩ | ⟨hm, ⟨h1, -⟩ | ⟨h3', -⟩⟩
    · rw [hpair, h0, hm]
      norm_num
    · rw [hpair, h1, hm]
      norm_num
    · rw [hpair, h1, hm]
      norm_num
    · rw [hpair, h2', hm]
      norm_num [h2]
    · rw [hpair, h1, hm]
      norm_num
    · rw [hpair, h3', hm]
      norm_num [h3]
  obtain ⟨d, hd, hsym⟩ := ggFLW_symmetrizer D hTree (fun i j => α i (h j)) hP
  have hα : ∀ i, α i (h i) = 2 := by
    intro i
    rw [hpair, hC.1 i]
    norm_num
  have hspan := LinearAlgebra.Reflection.span_eq_top_of_scalar_mem_reflection_generated
    h α σ hσ s hs c hc hsc
  have hker := LinearAlgebra.Reflection.common_kernel_eq_zero_of_scalar_mem_reflection_generated
    h α σ hσ s hs c hc hsc
  obtain ⟨B, hB, hInv⟩ := ggFLW_invariantForm hp2 h α σ hσ hα hspan hker d hd hsym
  have hcl : ∀ t ∈ Subgroup.closure (Set.range σ), ∀ u v, B (t u) (t v) = B u v := by
    intro t ht
    induction ht using Subgroup.closure_induction with
    | mem t ht =>
      obtain ⟨i, rfl⟩ := ht
      exact hInv i
    | one => intro u v; rfl
    | mul a b _ _ ha hb =>
      intro u v
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ha, hb]
    | inv a _ ha =>
      intro u v
      change B (a.symm u) (a.symm v) = B u v
      have he := ha (a.symm u) (a.symm v)
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at he
      exact he.symm
  obtain ⟨par, i0, depth, hpar, hdepth⟩ := hTree
  have hhi : h i0 ≠ 0 := by
    intro hz
    have he := hα i0
    rw [hz, map_zero] at he
    exact h2 he.symm
  have hne : ¬ ∀ u, B (h i0) u = 0 := fun hz => hhi (hB (h i0) hz)
  obtain ⟨u, hu⟩ := not_forall.mp hne
  have he := hcl s hs (h i0) u
  rw [hsc, hsc] at he
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at he
  have he' : (c * c) * B (h i0) u = 1 * B (h i0) u := by
    simpa only [mul_assoc, one_mul] using he
  simpa only [pow_two] using mul_right_cancel₀ hu he'

end CFSG.StandardType
