module

public import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Isomorphisms

public section

namespace CFSG.StandardType.ZS

private theorem zga_bilin_linearCombination {K M ι : Type*} [Field K] [AddCommGroup M]
    [Module K M] [Fintype ι] (B : LinearMap.BilinForm K M) (v : ι → M) (c : ι → K) (j : ι) :
    B (Fintype.linearCombination K v c) (v j) = ∑ i, c i * B (v i) (v j) := by
  rw [Fintype.linearCombination_apply, map_sum, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul]

private theorem zga_ker_le_of_gram {K V W ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Fintype ι] {f : LinearMap.BilinForm K V}
    {B : LinearMap.BilinForm K W} {y : ι → V} {u : ι → W}
    (hB : ∀ x, (∀ w, B x w = 0) → x = 0) (hu : Submodule.span K (Set.range u) = ⊤)
    (hgram : ∀ i j, B (u i) (u j) = f (y i) (y j)) :
    LinearMap.ker (Fintype.linearCombination K y) ≤
      LinearMap.ker (Fintype.linearCombination K u) := by
  intro c hc
  rw [LinearMap.mem_ker] at hc ⊢
  apply hB
  intro w
  have hzero : B (Fintype.linearCombination K u c) = 0 := by
    refine (Submodule.linearMap_eq_zero_iff_of_span_eq_top
      (B (Fintype.linearCombination K u c)) hu).mpr ?_
    rintro ⟨w, i, rfl⟩
    rw [zga_bilin_linearCombination B u c i]
    have hs : ∑ j, c j * B (u j) (u i) = ∑ j, c j * f (y j) (y i) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hgram j i]
    rw [hs, ← zga_bilin_linearCombination f y c i, hc]
    simp
  rw [hzero]
  simp

private theorem zga_ker_le_of_gram_symm {K V W ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Fintype ι] {f : LinearMap.BilinForm K V}
    {B : LinearMap.BilinForm K W} {y : ι → V} {u : ι → W}
    (hf : ∀ x, (∀ v, f x v = 0) → x = 0) (hy : Submodule.span K (Set.range y) = ⊤)
    (hgram : ∀ i j, B (u i) (u j) = f (y i) (y j)) :
    LinearMap.ker (Fintype.linearCombination K u) ≤
      LinearMap.ker (Fintype.linearCombination K y) := by
  intro c hc
  rw [LinearMap.mem_ker] at hc ⊢
  apply hf
  intro v
  have hzero : f (Fintype.linearCombination K y c) = 0 := by
    refine (Submodule.linearMap_eq_zero_iff_of_span_eq_top
      (f (Fintype.linearCombination K y c)) hy).mpr ?_
    rintro ⟨v, i, rfl⟩
    rw [zga_bilin_linearCombination f y c i]
    have hs : ∑ j, c j * f (y j) (y i) = ∑ j, c j * B (u j) (u i) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← hgram j i]
    rw [hs, ← zga_bilin_linearCombination B u c i, hc]
    simp
  rw [hzero]
  simp

private theorem zga_isometry_of_gram {K V W ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Fintype ι] {f : LinearMap.BilinForm K V}
    {B : LinearMap.BilinForm K W} {y : ι → V} {u : ι → W}
    (hy : Submodule.span K (Set.range y) = ⊤)
    (hgram : ∀ i j, B (u i) (u j) = f (y i) (y j)) (L : V ≃ₗ[K] W)
    (hLi : ∀ i, L (y i) = u i) : ∀ x x', B (L x) (L x') = f x x' := by
  have hsecond : ∀ (j : ι) (x' : V), f (y j) x' = B (u j) (L x') := by
    intro j x'
    have hEqOn : Set.EqOn (f (y j)) ((B (u j)).comp (L : V →ₗ[K] W)) (Set.range y) := by
      rintro z ⟨i, rfl⟩
      show f (y j) (y i) = ((B (u j)).comp (L : V →ₗ[K] W)) (y i)
      rw [LinearMap.comp_apply]
      change f (y j) (y i) = B (u j) (L (y i))
      rw [hLi i, hgram j i]
    exact LinearMap.eqOn_span hEqOn (x := x') (by rw [hy]; exact Submodule.mem_top)
  intro x x'
  have hEqOn : Set.EqOn (f.flip x') ((B.flip (L x')).comp (L : V →ₗ[K] W))
      (Set.range y) := by
    rintro z ⟨i, rfl⟩
    show f.flip x' (y i) = ((B.flip (L x')).comp (L : V →ₗ[K] W)) (y i)
    rw [LinearMap.comp_apply, LinearMap.BilinForm.flip_apply]
    change f (y i) x' = B (L (y i)) (L x')
    rw [hLi i]
    exact hsecond i x'
  have h := LinearMap.eqOn_span hEqOn (x := x) (by rw [hy]; exact Submodule.mem_top)
  simpa only [LinearMap.comp_apply, LinearMap.BilinForm.flip_apply,
    LinearEquiv.coe_toLinearMap] using h.symm

theorem exists_linearEquiv_of_gram_eq {K V W ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Fintype ι] {f : LinearMap.BilinForm K V}
    {B : LinearMap.BilinForm K W} (hf : ∀ x, (∀ y, f x y = 0) → x = 0)
    (hB : ∀ x, (∀ y, B x y = 0) → x = 0) {y : ι → V} {u : ι → W}
    (hy : Submodule.span K (Set.range y) = ⊤) (hu : Submodule.span K (Set.range u) = ⊤)
    (hgram : ∀ i j, B (u i) (u j) = f (y i) (y j)) :
    ∃ L : V ≃ₗ[K] W, (∀ i, L (y i) = u i) ∧ ∀ x x', B (L x) (L x') = f x x' := by
  classical
  have hcy : Function.Surjective (Fintype.linearCombination K y) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hy]
  have hcu : Function.Surjective (Fintype.linearCombination K u) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hu]
  have hker_le := zga_ker_le_of_gram hB hu hgram
  have hker_le' := zga_ker_le_of_gram_symm hf hy hgram
  have hker : LinearMap.ker (Fintype.linearCombination K y) =
      LinearMap.ker (Fintype.linearCombination K u) := le_antisymm hker_le hker_le'
  let L : V ≃ₗ[K] W :=
    (((Fintype.linearCombination K y).quotKerEquivOfSurjective hcy).symm.trans
      (Submodule.quotEquivOfEq (LinearMap.ker (Fintype.linearCombination K y))
        (LinearMap.ker (Fintype.linearCombination K u)) hker)).trans
      ((Fintype.linearCombination K u).quotKerEquivOfSurjective hcu)
  have hL : ∀ c : ι → K, L (Fintype.linearCombination K y c) =
      Fintype.linearCombination K u c := by
    intro c
    dsimp only [L]
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply,
      LinearMap.quotKerEquivOfSurjective_symm_apply (Fintype.linearCombination K y) hcy c,
      Submodule.quotEquivOfEq_mk]
    exact LinearMap.quotKerEquivOfSurjective_apply_mk
      (Fintype.linearCombination K u) hcu c
  have hLi : ∀ i, L (y i) = u i := by
    intro i
    have hyi : Fintype.linearCombination K y (Pi.single i 1) = y i := by
      rw [Fintype.linearCombination_apply_single, one_smul]
    have hui : Fintype.linearCombination K u (Pi.single i 1) = u i := by
      rw [Fintype.linearCombination_apply_single, one_smul]
    rw [← hyi, hL, hui]
  exact ⟨L, hLi, zga_isometry_of_gram hy hgram L hLi⟩

end CFSG.StandardType.ZS
