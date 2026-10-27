module

public import Mathlib.LinearAlgebra.Eigenspace.Pi
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

public section

namespace CFSG.RankThree.PartOne.S15K

open Polynomial Module

variable {E W : Type*} [Field E] [AddCommGroup W] [Module E W]

theorem ker_aeval_X_sub_C (T : Module.End E W) (a : E) :
    LinearMap.ker (aeval T (X - C a : E[X])) = T.eigenspace a := by
  ext w
  rw [LinearMap.mem_ker, Module.End.mem_eigenspace_iff]
  simp [sub_eq_zero, Algebra.algebraMap_eq_smul_one]

theorem iSup_ker_prod_aeval (T : Module.End E W) (s : Finset E) :
    LinearMap.ker (aeval T (∏ μ ∈ s, (X - C μ) : E[X])) = ⨆ μ ∈ s, T.eigenspace μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, map_one, Finset.notMem_empty, iSup_false, iSup_bot]
    rw [Module.End.one_eq_id, LinearMap.ker_id]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.iSup_insert]
    have hcop : IsCoprime (X - C a : E[X]) (∏ μ ∈ s, (X - C μ) : E[X]) := by
      refine IsCoprime.prod_right fun μ hμ => ?_
      refine Polynomial.isCoprime_X_sub_C_of_isUnit_sub ?_
      have : a ≠ μ := fun h => ha (h ▸ hμ)
      exact IsUnit.mk0 _ (sub_ne_zero.mpr this)
    rw [← Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime T hcop, ker_aeval_X_sub_C, ih]

theorem iSup_eigenspace_eq_top_of_pow_eq_one {p : ℕ} (hp : 0 < p) {ζ : E}
    (hζ : IsPrimitiveRoot ζ p) {T : Module.End E W} (hT : T ^ p = 1) :
    ⨆ μ ∈ nthRootsFinset p (1 : E), T.eigenspace μ = ⊤ := by
  rw [← iSup_ker_prod_aeval, ← Polynomial.X_pow_sub_one_eq_prod hp hζ]
  have : aeval T (X ^ p - 1 : E[X]) = 0 := by simp [hT]
  rw [this]
  exact LinearMap.ker_zero

theorem iSup_iInf_eigenspace_eq_top {ι : Type*} [FiniteDimensional E W] {p : ℕ} (hp : 0 < p)
    (hpE : (p : E) ≠ 0) {ζ : E} (hζ : IsPrimitiveRoot ζ p) (T : ι → Module.End E W)
    (hcomm : Pairwise fun i j => Commute (T i) (T j)) (hT : ∀ i, T i ^ p = 1) :
    ⨆ χ : ι → E, ⨅ i, (T i).eigenspace (χ i) = ⊤ := by
  have hsq : Squarefree (X ^ p - 1 : E[X]) :=
    (Polynomial.separable_X_pow_sub_C (1 : E) hpE one_ne_zero).squarefree
  have hsemi : ∀ i, (T i).IsSemisimple := fun i =>
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq (by simp [hT i])
  have hfs : ∀ i, (T i).IsFinitelySemisimple := fun i =>
    Module.End.isFinitelySemisimple_iff_isSemisimple.mpr (hsemi i)
  have hmax : ∀ i, ⨆ μ, (T i).maxGenEigenspace μ = ⊤ := fun i => by
    simp only [(hfs i).maxGenEigenspace_eq_eigenspace]
    refine eq_top_iff.mpr ?_
    rw [← iSup_eigenspace_eq_top_of_pow_eq_one hp hζ (hT i)]
    exact iSup₂_le fun μ _ => le_iSup (fun μ => (T i).eigenspace μ) μ
  have h := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    T hcomm hmax
  simpa only [(hfs _).maxGenEigenspace_eq_eigenspace] using h

theorem stable_le_iSup_iInf_eigenspace {ι : Type*} [FiniteDimensional E W] {p : ℕ} (hp : 0 < p)
    (hpE : (p : E) ≠ 0) {ζ : E} (hζ : IsPrimitiveRoot ζ p) (T : ι → Module.End E W)
    (hcomm : Pairwise fun i j => Commute (T i) (T j)) (hT : ∀ i, T i ^ p = 1)
    (N : Submodule E W) (hN : ∀ i, ∀ w ∈ N, T i w ∈ N) :
    N ≤ ⨆ χ : ι → E, (N ⊓ ⨅ i, (T i).eigenspace (χ i)) := by
  classical
  let T' : ι → Module.End E N := fun i => (T i).restrict (hN i)
  have hcoe : ∀ (i : ι) (n : N), ((T' i n : N) : W) = T i (n : W) := fun i n => rfl
  have hpow : ∀ (i : ι) (k : ℕ) (n : N), (((T' i ^ k) n : N) : W) = (T i ^ k) (n : W) := by
    intro i k
    induction k with
    | zero => intro n; rfl
    | succ k ih =>
      intro n
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
      rfl
  have hT' : ∀ i, T' i ^ p = 1 := fun i =>
    LinearMap.ext fun n => Subtype.ext (by rw [hpow, hT]; rfl)
  have hcomm' : Pairwise fun i j => Commute (T' i) (T' j) := fun i j hij =>
    LinearMap.ext fun n => Subtype.ext (by
      have := congrArg (fun A : Module.End E W => A (n : W)) (hcomm hij).eq
      simpa [Module.End.mul_apply, hcoe] using this)
  have h := iSup_iInf_eigenspace_eq_top hp hpE hζ T' hcomm' hT'
  intro w hw
  have hw' : (⟨w, hw⟩ : N) ∈ ⨆ χ : ι → E, ⨅ i, (T' i).eigenspace (χ i) := by rw [h]; trivial
  have hmap : Submodule.map N.subtype (⨆ χ : ι → E, ⨅ i, (T' i).eigenspace (χ i)) ≤
      ⨆ χ : ι → E, (N ⊓ ⨅ i, (T i).eigenspace (χ i)) := by
    rw [Submodule.map_iSup]
    refine iSup_mono fun χ => ?_
    rintro _ ⟨n, hn, rfl⟩
    refine ⟨n.2, ?_⟩
    have hn' : n ∈ (⨅ i, (T' i).eigenspace (χ i) : Submodule E N) := hn
    show (n : W) ∈ (⨅ i, (T i).eigenspace (χ i) : Submodule E W)
    rw [Submodule.mem_iInf] at hn' ⊢
    intro i
    have := hn' i
    rw [Module.End.mem_eigenspace_iff] at this ⊢
    have h2 := congrArg (fun z : N => (z : W)) this
    simpa [hcoe] using h2
  exact hmap ⟨⟨w, hw⟩, hw', rfl⟩

end CFSG.RankThree.PartOne.S15K
