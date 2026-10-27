module

public import Mathlib.Algebra.DirectSum.LinearMap
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.Order.BourbakiWitt
public import Mathlib.Order.CompletePartialOrder
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.Unbundled
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit

namespace CFSG
end CFSG
open CFSG
/-!
# Peterfalvi, Section 1, Proposition (1.1)

This file is the Lean target for `PFtest/Blueprint/section1/proposition_1_1.tex`.

Current scope discipline:

* Only Mathlib modules and `PFtest/Ind.lean` are imported.
* No Lean files outside `PFtest` are imported or read.
* Theorem proofs are introduced in blueprint order and should be decomposed
  into named local nodes before being closed directly.
-/

noncomputable section

attribute [local instance] Fintype.ofFinite

open scoped BigOperators

namespace CFSG.Section1
universe u
universe v

/-! ## Basic notation from the text -/

public abbrev ClassFunction (G : Type*) := G → ℂ
@[expose] public def IsClassFunction {G : Type*} [Group G] (f : ClassFunction G) : Prop :=
  ∀ x g : G, f (x * g * x⁻¹) = f g

def classFunctionSupport {G : Type*} (f : ClassFunction G) : Set G :=
  {g | f g ≠ 0}

private def supportedOn {G : Type*} (f : ClassFunction G) (A : Set G) : Prop :=
  classFunctionSupport f ⊆ A

private def scalarProduct (G : Type*) [Finite G] (α β : ClassFunction G) : ℂ :=
  (Nat.card G : ℂ)⁻¹ * ∑ g : G, α g * star (β g)

@[expose] public def principalCharacter (G : Type*) : ClassFunction G :=
  fun _ => 1

@[simp]
public theorem principalCharacter_apply {G : Type*} (g : G) :
    principalCharacter G g = 1 := rfl

@[expose] public def conjugateCharacter {G : Type*} (χ : ClassFunction G) : ClassFunction G :=
  fun g => star (χ g)

def IsTISubset {G : Type*} [Group G] (A : Set G) : Prop :=
  ∀ g : G, (∀ x, x ∈ A → g * x * g⁻¹ ∈ A) →
    Disjoint ((fun x => g * x * g⁻¹) '' A) A

def punctured {G : Type*} [One G] (A : Set G) : Set G :=
  A \ {1}


/-! ## Small group-theoretic nodes for Proposition (1.1) -/

lemma mem_zpowers_sq_of_odd_order {G : Type*} [Group G] (x : G)
    (hodd : Odd (orderOf x)) :
    x ∈ Subgroup.zpowers (x ^ 2) := by
  rcases hodd with ⟨m, hm⟩
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨Int.ofNat (m + 1), ?_⟩
  calc
    (x ^ 2) ^ (↑m + 1 : ℤ) = (x ^ 2) ^ ((m + 1 : ℕ) : ℤ) := by
      norm_num
    _ = (x ^ 2) ^ (m + 1) := by
      rw [zpow_natCast]
    _ = x ^ (2 * (m + 1)) := by
      rw [pow_mul]
    _ = x ^ (2 * m + 2) := by
      ring_nf
    _ = x ^ (orderOf x + 1) := by
      rw [hm]
    _ = x := by
      rw [pow_add, pow_orderOf_eq_one, one_mul, pow_one]

lemma mem_zpowers_sq_of_odd_card {G : Type*} [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) (x : G) :
    x ∈ Subgroup.zpowers (x ^ 2) := by
  have hdiv : orderOf x ∣ Nat.card G := by
    exact orderOf_dvd_natCard x
  exact mem_zpowers_sq_of_odd_order x (Odd.of_dvd_nat hodd hdiv)

public lemma eq_one_of_conj_eq_inv_of_odd_card {G : Type*} [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) {g x : G}
    (hx : x * g * x⁻¹ = g⁻¹) :
    g = 1 := by
  have hx2_conj : x ^ 2 * g * (x ^ 2)⁻¹ = g := by
    calc
      x ^ 2 * g * (x ^ 2)⁻¹ = x * (x * g * x⁻¹) * x⁻¹ := by
        simp [pow_two, mul_assoc]
      _ = x * g⁻¹ * x⁻¹ := by
        rw [hx]
      _ = (x * g * x⁻¹)⁻¹ := by
        group
      _ = (g⁻¹)⁻¹ := by
        rw [hx]
      _ = g := by
        simp
  have hx2_comm : x ^ 2 ∈ Subgroup.centralizer ({g} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hmul := congrArg (fun y => y * x ^ 2) hx2_conj
    simpa [mul_assoc] using hmul
  have hx_zpowers : x ∈ Subgroup.zpowers (x ^ 2) :=
    mem_zpowers_sq_of_odd_card hodd x
  have hx_comm_mem : x ∈ Subgroup.centralizer ({g} : Set G) := by
    exact (Subgroup.zpowers_le.mpr hx2_comm) hx_zpowers
  have hx_comm : x * g = g * x := by
    exact Subgroup.mem_centralizer_singleton_iff.mp hx_comm_mem
  have hg_inv_eq : g⁻¹ = g := by
    calc
      g⁻¹ = x * g * x⁻¹ := hx.symm
      _ = g := by
        calc
          x * g * x⁻¹ = (g * x) * x⁻¹ := by
            rw [hx_comm]
          _ = g := by
            simp [mul_assoc]
  have hg_sq : g ^ 2 = 1 := by
    rw [pow_two]
    calc
      g * g = g * g⁻¹ := by
        rw [hg_inv_eq]
      _ = 1 := by
        simp
  have horder_dvd_two : orderOf g ∣ 2 := by
    exact orderOf_dvd_iff_pow_eq_one.mpr hg_sq
  have horder_odd : Odd (orderOf g) := by
    have hdiv : orderOf g ∣ Nat.card G := by
      exact orderOf_dvd_natCard g
    exact Odd.of_dvd_nat hodd hdiv
  have horder_le_two : orderOf g ≤ 2 := by
    exact Nat.le_of_dvd (by decide : 0 < 2) horder_dvd_two
  rcases horder_odd with ⟨k, hk⟩
  have horder_eq_one : orderOf g = 1 := by
    omega
  exact orderOf_eq_one_iff.mp horder_eq_one

/-! ## Linear-algebra core of Isaacs Theorem 6.32 -/


/-! ## Conjugacy-class side of Proposition (1.1) -/


/-! ## Proposition (1.1) -/

public lemma end_isSemisimple_of_pow_eq_one
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) {n : ℕ} (hn : n ≠ 0) (hpow : f ^ n = 1) :
    f.IsSemisimple := by
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (p := ((Polynomial.X : Polynomial ℂ) ^ n - 1)) ?_ ?_
  · exact
      ((Polynomial.X_pow_sub_one_separable_iff (F := ℂ) (n := n)).2 (by
        exact_mod_cast hn)).squarefree
  · simp [map_sub, map_pow, Polynomial.aeval_X, hpow]

public lemma eigenvalue_pow_eq_one_of_pow_eq_one
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {f : Module.End ℂ V} {μ : ℂ} {n : ℕ}
    (hpow : f ^ n = 1) (hμ : f.HasEigenvalue μ) :
    μ ^ n = 1 := by
  rcases hμ.exists_hasEigenvector with ⟨v, hv⟩
  have hvpow : (f ^ n) v = μ ^ n • v := hv.pow_apply n
  have hv_eq : v = μ ^ n • v := by
    simpa [hpow] using hvpow
  have hsmul : (1 - μ ^ n) • v = 0 := by
    rw [sub_smul, one_smul, ← hv_eq, sub_self]
  rcases smul_eq_zero.mp hsmul with hzero | hzero
  · exact (sub_eq_zero.mp hzero).symm
  · exact (hv.2 hzero).elim


lemma eigenvalue_ne_zero_of_pow_eq_one
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {f : Module.End ℂ V} {μ : ℂ} {n : ℕ}
    (hn : n ≠ 0) (hpow : f ^ n = 1) (hμ : f.HasEigenvalue μ) :
    μ ≠ 0 := by
  have hμpow : μ ^ n = 1 := eigenvalue_pow_eq_one_of_pow_eq_one hpow hμ
  intro hzero
  rw [hzero] at hμpow
  simp [hn] at hμpow

lemma eigenvalue_unit_mem_rootsOfUnity_of_pow_eq_one
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {f : Module.End ℂ V} {μ : ℂ} {n : ℕ} [NeZero n]
    (hpow : f ^ n = 1) (hμ : f.HasEigenvalue μ) :
    (Units.mk0 μ
      (eigenvalue_ne_zero_of_pow_eq_one (n := n) (show n ≠ 0 from NeZero.ne n) hpow hμ) : ℂˣ) ∈
        rootsOfUnity n ℂ := by
  rw [mem_rootsOfUnity]
  ext
  simpa using eigenvalue_pow_eq_one_of_pow_eq_one hpow hμ

lemma complex_star_eigenvalue_eq_inv_of_pow_eq_one
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {f : Module.End ℂ V} {μ : ℂ} {n : ℕ} [NeZero n]
    (hpow : f ^ n = 1) (hμ : f.HasEigenvalue μ) :
    star μ = μ⁻¹ := by
  simpa using
    (Complex.conj_rootsOfUnity
      (ζ := Units.mk0 μ
        (eigenvalue_ne_zero_of_pow_eq_one (n := n) (show n ≠ 0 from NeZero.ne n) hpow hμ))
      (n := n) (eigenvalue_unit_mem_rootsOfUnity_of_pow_eq_one (n := n) hpow hμ))

lemma complex_star_eigenvalue_eq_pow_pred_of_pow_eq_one
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {f : Module.End ℂ V} {μ : ℂ} {n : ℕ}
    (hn : n ≠ 0) (hpow : f ^ n = 1) (hμ : f.HasEigenvalue μ) :
    star μ = μ ^ (n - 1) := by
  haveI : NeZero n := ⟨hn⟩
  rw [complex_star_eigenvalue_eq_inv_of_pow_eq_one (n := n) hpow hμ]
  rcases Nat.exists_eq_succ_of_ne_zero hn with ⟨m, rfl⟩
  apply inv_eq_of_mul_eq_one_right
  simpa [pow_succ', mul_comm, mul_left_comm, mul_assoc] using
    eigenvalue_pow_eq_one_of_pow_eq_one hpow hμ

public lemma eigenspace_iSup_eq_top_over_eigenvalues
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {f : Module.End ℂ V} (hf : f.IsSemisimple) :
    ⨆ μ : f.Eigenvalues, f.eigenspace (μ : ℂ) = ⊤ := by
  calc
    ⨆ μ : f.Eigenvalues, f.eigenspace (μ : ℂ) = ⨆ μ : ℂ, f.eigenspace μ := by
      apply le_antisymm
      · exact iSup_le fun μ => le_iSup (fun ν : ℂ => f.eigenspace ν) μ
      · refine iSup_le fun μ => ?_
        by_cases hμ : f.HasEigenvalue μ
        · exact le_iSup (fun ν : f.Eigenvalues => f.eigenspace (ν : ℂ)) ⟨μ, hμ⟩
        · have hbot : f.eigenspace μ = ⊥ := by
            by_contra hne
            exact hμ hne
          simp [hbot]
    _ = ⊤ := hf.iSup_eigenspace_eq_top

public lemma trace_restrict_pow_eigenspace_eq
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {f : Module.End ℂ V} (μ : f.Eigenvalues) (k : ℕ) :
    LinearMap.trace ℂ (f.eigenspace (μ : ℂ))
      ((f ^ k).restrict
        (Module.End.pow_apply_mem_of_forall_mem k
          (f.mem_invtSubmodule_iff_forall_mem_of_mem.mp
            (Module.End.eigenspace_mem_invtSubmodule f (μ : ℂ))))) =
      (μ : ℂ) ^ k * Module.finrank ℂ (f.eigenspace (μ : ℂ)) := by
  let hμ :
      ∀ x : V, x ∈ f.eigenspace (μ : ℂ) → f x ∈ f.eigenspace (μ : ℂ) :=
    f.mem_invtSubmodule_iff_forall_mem_of_mem.mp
      (Module.End.eigenspace_mem_invtSubmodule f (μ : ℂ))
  have hrestrict :
      ((f ^ k).restrict (Module.End.pow_apply_mem_of_forall_mem k hμ)) =
        ((μ : ℂ) ^ k • LinearMap.id : Module.End ℂ (f.eigenspace (μ : ℂ))) := by
    calc
      ((f ^ k).restrict (Module.End.pow_apply_mem_of_forall_mem k hμ)) = (f.restrict hμ) ^ k := by
        symm
        exact Module.End.pow_restrict k hμ
      _ = (((μ : ℂ) • LinearMap.id : Module.End ℂ (f.eigenspace (μ : ℂ))) ^ k) := by
        rw [Module.End.restrict_eigenspace]
      _ = ((μ : ℂ) ^ k • (LinearMap.id : Module.End ℂ (f.eigenspace (μ : ℂ)))) := by
        simpa using smul_pow (μ : ℂ) (LinearMap.id : Module.End ℂ (f.eigenspace (μ : ℂ))) k
      _ = (μ : ℂ) ^ k • LinearMap.id := by
        simp
  rw [hrestrict]
  simp [LinearMap.trace_id, smul_eq_mul]

public lemma trace_pow_eq_sum_eigenvalues
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {f : Module.End ℂ V} {n k : ℕ}
    (hn : n ≠ 0) (hpow : f ^ n = 1) :
    LinearMap.trace ℂ V (f ^ k) =
      ∑ μ : f.Eigenvalues, ((μ : ℂ) ^ k * Module.finrank ℂ (f.eigenspace (μ : ℂ))) := by
  classical
  let N : f.Eigenvalues → Submodule ℂ V := fun μ => f.eigenspace (μ : ℂ)
  have hsemi : f.IsSemisimple := end_isSemisimple_of_pow_eq_one f hn hpow
  have hindep : iSupIndep N := by
    change iSupIndep (f.eigenspace ∘ (fun μ : f.Eigenvalues => (μ : ℂ)))
    exact f.eigenspaces_iSupIndep.comp Subtype.coe_injective
  have htop : iSup N = ⊤ := by
    simpa [N] using eigenspace_iSup_eq_top_over_eigenvalues (f := f) hsemi
  have hds : DirectSum.IsInternal N :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hindep htop
  have hmap : ∀ μ : f.Eigenvalues, Set.MapsTo (f ^ k) (N μ) (N μ) := by
    intro μ
    exact Module.End.pow_apply_mem_of_forall_mem k
      (f.mem_invtSubmodule_iff_forall_mem_of_mem.mp
        (Module.End.eigenspace_mem_invtSubmodule f (μ : ℂ)))
  calc
    LinearMap.trace ℂ V (f ^ k) =
      ∑ μ : f.Eigenvalues, LinearMap.trace ℂ (N μ) ((f ^ k).restrict (hmap μ)) := by
        simpa [N] using LinearMap.trace_eq_sum_trace_restrict hds hmap
    _ = ∑ μ : f.Eigenvalues, ((μ : ℂ) ^ k * Module.finrank ℂ (f.eigenspace (μ : ℂ))) := by
      refine Finset.sum_congr rfl ?_
      intro μ hμ
      simpa [N] using trace_restrict_pow_eigenspace_eq (f := f) μ k

lemma trace_pow_pred_eq_star_trace_of_pow_eq_one
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {f : Module.End ℂ V} {n : ℕ}
    (hn : n ≠ 0) (hpow : f ^ n = 1) :
    LinearMap.trace ℂ V (f ^ (n - 1)) = star (LinearMap.trace ℂ V f) := by
  classical
  have htrace :
      LinearMap.trace ℂ V f =
        ∑ μ : f.Eigenvalues, ((μ : ℂ) * Module.finrank ℂ (f.eigenspace (μ : ℂ))) := by
    simpa using (trace_pow_eq_sum_eigenvalues (f := f) (n := n) (k := 1) hn hpow)
  have htracePred :
      LinearMap.trace ℂ V (f ^ (n - 1)) =
        ∑ μ : f.Eigenvalues, ((μ : ℂ) ^ (n - 1) * Module.finrank ℂ (f.eigenspace (μ : ℂ))) := by
    simpa using (trace_pow_eq_sum_eigenvalues (f := f) (n := n) (k := n - 1) hn hpow)
  rw [htracePred, htrace]
  calc
    ∑ μ : f.Eigenvalues, ((μ : ℂ) ^ (n - 1) * Module.finrank ℂ (f.eigenspace (μ : ℂ))) =
      ∑ μ : f.Eigenvalues, star (((μ : ℂ) * Module.finrank ℂ (f.eigenspace (μ : ℂ))) : ℂ) := by
        refine Finset.sum_congr rfl ?_
        intro μ hμ
        rw [star_mul]
        simp [complex_star_eigenvalue_eq_pow_pred_of_pow_eq_one (f := f) (μ := (μ : ℂ)) hn hpow
          μ.property, mul_comm]
    _ = star (∑ μ : f.Eigenvalues, ((μ : ℂ) * Module.finrank ℂ (f.eigenspace (μ : ℂ))) : ℂ) := by
      symm
      simp

def matrixLeftMul {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) :
    Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ where
  toFun := fun M => A * M
  map_add' _ _ := Matrix.mul_add _ _ _
  map_smul' c M := Matrix.mul_smul A c M

def matrixRightMul {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) :
    Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ where
  toFun := fun M => M * A
  map_add' _ _ := Matrix.add_mul _ _ _
  map_smul' c M := Matrix.smul_mul c M A

lemma matrix_stdBasis_repr_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (i j : ι) :
    (Matrix.stdBasis ℂ ι ι).repr M (i, j) = M i j := by
  simp [Matrix.stdBasis]

lemma trace_matrix_flip_mulLeft_mulRight
    {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    LinearMap.trace ℂ (Matrix ι ι ℂ)
      ((LinearEquiv.toLinearMap (Matrix.transposeLinearEquiv ι ι ℂ ℂ)).comp
        ((matrixLeftMul (Matrix.transpose A)).comp
        (matrixRightMul A))) =
      Matrix.trace (A * A) := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Matrix.stdBasis ℂ ι ι), Matrix.trace]
  rw [Fintype.sum_prod_type]
  simp [LinearMap.toMatrix_apply, Matrix.stdBasis_eq_single, Matrix.mul_apply,
    matrix_stdBasis_repr_apply, Matrix.trace]
  have hinner : ∀ x x' y' : ι,
      (∑ y : ι, if x' = x then if y = y' then A y x' else 0 else 0) =
        if x' = x then A y' x' else 0 := by
    intro x x' y'
    by_cases h : x' = x
    · simp [h]
    · simp [h]
  have hinner2 : ∀ x x₁ x₂ : ι,
      (∑ x₃ : ι, if x = x₂ ∧ x₁ = x₃ then A x₃ x else 0) =
        if x = x₂ then A x₁ x else 0 := by
    intro x x₁ x₂
    by_cases h : x = x₂
    · simp [h]
    · simp [h]
  simp [matrixLeftMul, matrixRightMul, Matrix.mul_apply, Matrix.single_apply, hinner2, mul_comm]

lemma bilinForm_toMatrix_flip
    {ι : Type*} [Fintype ι] [DecidableEq ι] {W : Type*}
    [AddCommMonoid W] [Module ℂ W] (b : Module.Basis ι ℂ W)
    (B : LinearMap.BilinForm ℂ W) :
    LinearMap.BilinForm.toMatrix b
        (((LinearMap.BilinForm.flipHom :
            LinearMap.BilinForm ℂ W ≃ₗ[ℂ] LinearMap.BilinForm ℂ W).toLinearMap) B) =
      (LinearMap.BilinForm.toMatrix b B).transpose := by
  ext i j
  simp [LinearMap.BilinForm.flip_apply]

public lemma representation_character_inv_eq_star_character
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    ρ.character g⁻¹ = star (ρ.character g) := by
  let n := orderOf g
  have hn : n ≠ 0 := Nat.ne_of_gt (orderOf_pos g)
  have hpow : (ρ g) ^ n = 1 := by
    subst n
    rw [← MonoidHom.map_pow, pow_orderOf_eq_one, MonoidHom.map_one]
  have hginv : g ^ (n - 1) = g⁻¹ := by
    subst n
    have hmul : g ^ (orderOf g - 1) * g = 1 := by
      calc
        g ^ (orderOf g - 1) * g = g ^ ((orderOf g - 1) + 1) := by
          rw [pow_succ]
        _ = g ^ orderOf g := by
          congr 1
          exact Nat.sub_add_cancel (Nat.succ_le_of_lt (orderOf_pos g))
        _ = 1 := pow_orderOf_eq_one g
    exact eq_inv_iff_mul_eq_one.mpr hmul
  calc
    ρ.character g⁻¹ = LinearMap.trace ℂ V (ρ g⁻¹) := rfl
    _ = LinearMap.trace ℂ V ((ρ g) ^ (n - 1)) := by
      rw [← hginv, MonoidHom.map_pow]
    _ = star (LinearMap.trace ℂ V (ρ g)) := by
      simpa using trace_pow_pred_eq_star_trace_of_pow_eq_one (f := ρ g) (n := n) hn hpow
    _ = star (ρ.character g) := rfl

lemma representation_character_eq_inv_of_fixed_conjugate
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V)
    (hfixed : ρ.character = conjugateCharacter ρ.character) (g : G) :
    ρ.character g = ρ.character g⁻¹ := by
  have hreal : star (ρ.character g) = ρ.character g := by
    simpa [conjugateCharacter] using (congrFun hfixed g).symm
  calc
    ρ.character g = star (ρ.character g) := hreal.symm
    _ = ρ.character g⁻¹ := (representation_character_inv_eq_star_character ρ g).symm

lemma representation_dual_character_eq_of_fixed_conjugate
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V)
    (hfixed : ρ.character = conjugateCharacter ρ.character) :
    ρ.dual.character = ρ.character := by
  ext g
  rw [Representation.char_dual]
  symm
  exact representation_character_eq_inv_of_fixed_conjugate ρ hfixed g

lemma representation_self_dual_hom_finrank_eq_one_of_fixed_conjugate
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V)
    (hρ_irreducible : Representation.IsIrreducible ρ)
    (hfixed : ρ.character = conjugateCharacter ρ.character) :
    Module.finrank ℂ (Representation.IntertwiningMap ρ ρ.dual) = 1 := by
  classical
  have hchars : ρ.dual.character = ρ.character :=
    representation_dual_character_eq_of_fixed_conjugate ρ hfixed
  have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩ : Nat.card G ≠ 0)
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hcard_ne
  letI : Representation.IsIrreducible ρ := hρ_irreducible
  have horth :
      (Nat.card G : ℂ)⁻¹ * ∑ g : G, ρ.character g * ρ.character g⁻¹ = 1 := by
    have h := Representation.char_orthonormal (ρ := ρ) (σ := ρ)
    have hnonempty : Nonempty (ρ.Equiv ρ) := ⟨Representation.Equiv.refl ρ⟩
    simpa [hnonempty] using h
  have hscalar :
      (Nat.card G : ℂ)⁻¹ * ∑ g : G, ρ.dual.character g * ρ.character g⁻¹ =
        Module.finrank ℂ (Representation.IntertwiningMap ρ ρ.dual) := by
    simpa using
      (Representation.card_inv_mul_sum_char_mul_char_eq_finrank (ρ := ρ) (σ := ρ.dual))
  rw [hchars, horth] at hscalar
  exact_mod_cast hscalar.symm

lemma representation_exists_nonzero_hom_to_dual_of_fixed_conjugate
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V)
    (hρ_irreducible : Representation.IsIrreducible ρ)
    (hfixed : ρ.character = conjugateCharacter ρ.character) :
    ∃ f : Representation.IntertwiningMap ρ ρ.dual, f ≠ 0 := by
  classical
  have hfinrank :
      Module.finrank ℂ (Representation.IntertwiningMap ρ ρ.dual) = 1 :=
    representation_self_dual_hom_finrank_eq_one_of_fixed_conjugate ρ hρ_irreducible hfixed
  by_contra hzero
  push Not at hzero
  have hsub :
      Subsingleton (Representation.IntertwiningMap ρ ρ.dual) := by
    refine ⟨fun f g => ?_⟩
    rw [hzero f, hzero g]
  have hfinrank_zero :
      Module.finrank ℂ (Representation.IntertwiningMap ρ ρ.dual) = 0 :=
    Module.finrank_zero_of_subsingleton
  omega

public lemma representation_flip_linHom_dual_comm
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    ((LinearMap.BilinForm.flipHom :
        LinearMap.BilinForm ℂ V ≃ₗ[ℂ] LinearMap.BilinForm ℂ V).toLinearMap).comp
        ((Representation.linHom ρ ρ.dual) g) =
      ((Representation.linHom ρ ρ.dual) g).comp
        ((LinearMap.BilinForm.flipHom :
          LinearMap.BilinForm ℂ V ≃ₗ[ℂ] LinearMap.BilinForm ℂ V).toLinearMap) := by
  ext B x y
  simp [Representation.linHom_apply, LinearMap.BilinForm.flip_apply, Module.Dual.transpose_apply]

public lemma representation_linHom_dual_invariants_finrank_eq_one_of_fixed_conjugate
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V)
    (hρ_irreducible : Representation.IsIrreducible ρ)
    (hfixed : ρ.character = conjugateCharacter ρ.character) :
    Module.finrank ℂ
      (Representation.invariants (Representation.linHom ρ ρ.dual)) = 1 := by
  calc
    Module.finrank ℂ
        (Representation.invariants (Representation.linHom ρ ρ.dual)) =
      Module.finrank ℂ (Representation.IntertwiningMap ρ ρ.dual) := by
        simpa using
          (Representation.invariantsEquivIntertwiningMap (ρ := ρ) (σ := ρ.dual)).finrank_eq
    _ = 1 :=
      representation_self_dual_hom_finrank_eq_one_of_fixed_conjugate ρ hρ_irreducible hfixed

lemma representation_linHom_dual_apply_eq_comp
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G)
    (B : LinearMap.BilinForm ℂ V) :
    (Representation.linHom ρ ρ.dual g) B =
      B.comp (ρ g⁻¹) (ρ g⁻¹) := by
  ext x y
  rfl

public lemma representation_trace_flip_linHom_dual_eq_character_inv_mul_inv
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    LinearMap.trace ℂ (LinearMap.BilinForm ℂ V)
      (((LinearMap.BilinForm.flipHom :
            LinearMap.BilinForm ℂ V ≃ₗ[ℂ] LinearMap.BilinForm ℂ V).toLinearMap).comp
        ((Representation.linHom ρ ρ.dual) g)) =
      ρ.character (g⁻¹ * g⁻¹) := by
  classical
  let ι := Module.Free.ChooseBasisIndex ℂ V
  let b : Module.Basis ι ℂ V := Module.Free.chooseBasis ℂ V
  let A : Matrix ι ι ℂ := LinearMap.toMatrix b b (ρ g⁻¹)
  let F :
      LinearMap.BilinForm ℂ V →ₗ[ℂ] LinearMap.BilinForm ℂ V :=
    (((LinearMap.BilinForm.flipHom :
        LinearMap.BilinForm ℂ V ≃ₗ[ℂ] LinearMap.BilinForm ℂ V).toLinearMap).comp
      ((Representation.linHom ρ ρ.dual) g))
  calc
    LinearMap.trace ℂ (LinearMap.BilinForm ℂ V) F =
        LinearMap.trace ℂ (Matrix ι ι ℂ)
          ((LinearMap.BilinForm.toMatrix b).conj F) := by
          symm
          exact LinearMap.trace_conj' F (LinearMap.BilinForm.toMatrix b)
    _ =
        LinearMap.trace ℂ (Matrix ι ι ℂ)
          ((LinearEquiv.toLinearMap (Matrix.transposeLinearEquiv ι ι ℂ ℂ)).comp
            ((matrixLeftMul (Matrix.transpose A)).comp (matrixRightMul A))) := by
          congr 1
          ext M i j
          simp only [LinearEquiv.conj_apply, F, LinearMap.comp_apply]
          rw [LinearMap.BilinForm.toMatrix_symm]
          rw [representation_linHom_dual_apply_eq_comp]
          have hflip :
              LinearMap.BilinForm.toMatrix b
                  (((LinearMap.BilinForm.flipHom :
                      LinearMap.BilinForm ℂ V ≃ₗ[ℂ] LinearMap.BilinForm ℂ V).toLinearMap)
                    ((Matrix.toBilin b M).comp (ρ g⁻¹) (ρ g⁻¹))) =
                (LinearMap.BilinForm.toMatrix b
                  ((Matrix.toBilin b M).comp (ρ g⁻¹) (ρ g⁻¹))).transpose := by
            exact
              bilinForm_toMatrix_flip b
                ((Matrix.toBilin b M).comp (ρ g⁻¹) (ρ g⁻¹))
          have hcomp :
              LinearMap.BilinForm.toMatrix b
                  ((Matrix.toBilin b M).comp (ρ g⁻¹) (ρ g⁻¹)) =
                (LinearMap.toMatrix b b (ρ g⁻¹)).transpose * M *
                  LinearMap.toMatrix b b (ρ g⁻¹) := by
            simpa [LinearMap.BilinForm.toMatrix_symm, mul_assoc] using
              (LinearMap.BilinForm.toMatrix_comp (b := b) (c := b)
                (B := Matrix.toBilin b M) (l := ρ g⁻¹) (r := ρ g⁻¹))
          calc
            ((LinearMap.BilinForm.toMatrix b)
                (((LinearMap.BilinForm.flipHom :
                    LinearMap.BilinForm ℂ V ≃ₗ[ℂ] LinearMap.BilinForm ℂ V).toLinearMap)
                  ((Matrix.toBilin b M).comp (ρ g⁻¹) (ρ g⁻¹)))) i j =
                ((LinearMap.BilinForm.toMatrix b
                  ((Matrix.toBilin b M).comp (ρ g⁻¹) (ρ g⁻¹))).transpose) i j := by
                    exact congrArg (fun N : Matrix ι ι ℂ => N i j) hflip
            _ = (((LinearMap.toMatrix b b (ρ g⁻¹)).transpose * M *
                    LinearMap.toMatrix b b (ρ g⁻¹)).transpose) i j := by
                    simpa using congrArg (fun N : Matrix ι ι ℂ => N j i) hcomp
            _ = ((A.transpose * (M * A)).transpose) i j := by
                    simp [A, mul_assoc]
            _ = (Matrix.transposeLinearEquiv ι ι ℂ ℂ
                  ((matrixLeftMul (Matrix.transpose A)) ((matrixRightMul A) M))) i j := by
                    rfl
    _ = Matrix.trace (A * A) := trace_matrix_flip_mulLeft_mulRight A
    _ = Matrix.trace (LinearMap.toMatrix b b ((ρ g⁻¹) * (ρ g⁻¹))) := by
          simp [A, LinearMap.toMatrix_mul]
    _ = LinearMap.trace ℂ V ((ρ g⁻¹) * (ρ g⁻¹)) := by
          symm
          exact LinearMap.trace_eq_matrix_trace ℂ b ((ρ g⁻¹) * (ρ g⁻¹))
    _ = LinearMap.trace ℂ V (ρ (g⁻¹ * g⁻¹)) := by
          rw [← MonoidHom.map_mul]
    _ = ρ.character (g⁻¹ * g⁻¹) := rfl

lemma sum_classFunction_inv_mul_inv_eq_sum_of_odd_card
    {G : Type*} [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) (χ : ClassFunction G) :
    ∑ g : G, χ (g⁻¹ * g⁻¹) = ∑ g : G, χ g := by
  have hsurj_sq : Function.Surjective (fun g : G => g * g) := by
    intro g
    have hg : g ∈ Subgroup.zpowers (g ^ 2) := mem_zpowers_sq_of_odd_card hodd g
    rw [Subgroup.mem_zpowers_iff] at hg
    rcases hg with ⟨z, hz⟩
    refine ⟨g ^ z, ?_⟩
    calc
      g ^ z * g ^ z = g ^ (z + z) := by rw [← zpow_add]
      _ = g ^ (z * 2) := by congr 1; ring
      _ = (g ^ ((2 : ℤ))) ^ z := by simpa using (zpow_mul' g z 2)
      _ = (g ^ 2) ^ z := by
        simpa using congrArg (fun t : G => t ^ z) (zpow_natCast g 2)
      _ = g := hz
  have hsurj : Function.Surjective (fun g : G => g⁻¹ * g⁻¹) := by
    intro g
    rcases hsurj_sq g with ⟨y, hy⟩
    refine ⟨y⁻¹, ?_⟩
    simp [hy]
  have hbij : Function.Bijective (fun g : G => g⁻¹ * g⁻¹) := hsurj.bijective_of_finite
  simpa using Fintype.sum_bijective (fun g : G => g⁻¹ * g⁻¹) hbij _ _ (fun g => rfl)

set_option maxHeartbeats 800000 in
lemma representation_average_character_ne_zero_of_fixed_conjugate
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (hodd : Odd (Nat.card G)) (ρ : Representation ℂ G V)
    (hρ_irreducible : Representation.IsIrreducible ρ)
    (hfixed : ρ.character = conjugateCharacter ρ.character) :
    ((Nat.card G : ℂ)⁻¹ * ∑ g : G, ρ.character g) ≠ 0 := by
  classical
  let ρh : Representation ℂ G (LinearMap.BilinForm ℂ V) :=
    Representation.linHom ρ ρ.dual
  let p : Submodule ℂ (LinearMap.BilinForm ℂ V) := Representation.invariants ρh
  let avg : LinearMap.BilinForm ℂ V →ₗ[ℂ] LinearMap.BilinForm ℂ V :=
    Representation.averageMap ρh
  let flip : LinearMap.BilinForm ℂ V →ₗ[ℂ] LinearMap.BilinForm ℂ V :=
    ((LinearMap.BilinForm.flipHom :
      LinearMap.BilinForm ℂ V ≃ₗ[ℂ] LinearMap.BilinForm ℂ V).toLinearMap)
  letI : Module.Free ℂ p := Module.Free.of_basis (Module.Basis.ofVectorSpace ℂ p)
  letI : Module.Finite ℂ p := Module.Finite.of_basis (Module.Basis.ofVectorSpace ℂ p)
  have hpfin : Module.finrank ℂ p = 1 := by
    simpa [p, ρh] using
      representation_linHom_dual_invariants_finrank_eq_one_of_fixed_conjugate
        ρ hρ_irreducible hfixed
  have havgProj : LinearMap.IsProj p avg := by
    simpa [p, avg, ρh] using (Representation.isProj_averageMap ρh)
  have hflip_mem : ∀ x ∈ p, flip x ∈ p := by
    intro x hx
    rw [Representation.mem_invariants] at hx ⊢
    intro g
    calc
      ρh g (flip x) = flip (ρh g x) := by
        have hcomm := congrArg
          (fun f : LinearMap.BilinForm ℂ V →ₗ[ℂ] LinearMap.BilinForm ℂ V => f x)
          (representation_flip_linHom_dual_comm ρ g)
        simpa [flip, ρh] using hcomm.symm
      _ = flip x := by rw [hx g]
  let flipP : p →ₗ[ℂ] p := flip.restrict hflip_mem
  let avgToP : LinearMap.BilinForm ℂ V →ₗ[ℂ] p := havgProj.codRestrict
  have hp_nonzero : ∃ x : p, x ≠ 0 := by
    rcases representation_exists_nonzero_hom_to_dual_of_fixed_conjugate
        ρ hρ_irreducible hfixed with ⟨f, hf⟩
    refine ⟨(Representation.invariantsEquivIntertwiningMap
      (ρ := ρ) (σ := ρ.dual)).symm f, ?_⟩
    intro hx
    apply hf
    exact (Representation.invariantsEquivIntertwiningMap
      (ρ := ρ) (σ := ρ.dual)).symm.injective <| by
      simpa using (show
        (Representation.invariantsEquivIntertwiningMap
          (ρ := ρ) (σ := ρ.dual)).symm f =
          (Representation.invariantsEquivIntertwiningMap
            (ρ := ρ) (σ := ρ.dual)).symm 0 from hx)
  have htrace_flipP_ne : LinearMap.trace ℂ p flipP ≠ 0 := by
    rcases hp_nonzero with ⟨x, hx⟩
    have hflipPx_ne : flipP x ≠ 0 := by
      intro hzero
      apply hx
      apply Subtype.ext
      apply (LinearMap.BilinForm.flipHom :
        LinearMap.BilinForm ℂ V ≃ₗ[ℂ] LinearMap.BilinForm ℂ V).injective
      simpa [flipP, flip] using congrArg Subtype.val hzero
    have hspan := (finrank_eq_one_iff_of_nonzero' (K := ℂ) (V := p) x hx).mp hpfin
    rcases hspan (flipP x) with ⟨c, hc⟩
    have hc_ne : c ≠ 0 := by
      intro hc0
      apply hflipPx_ne
      simpa [hc0] using hc.symm
    let b : Module.Basis Unit ℂ p := FiniteDimensional.basisSingleton Unit hpfin x hx
    have htrace_eq_c : LinearMap.trace ℂ p flipP = c := by
      rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
      have hxrepr_ne :
          (Module.basisUnique Unit hpfin).repr x PUnit.unit ≠ 0 := by
        exact mt (Module.basisUnique_repr_eq_zero_iff (ι := Unit) (h := hpfin)
          (v := x) (i := PUnit.unit)).mp hx
      have hrepr :
          (Module.basisUnique Unit hpfin).repr (flipP x) PUnit.unit =
            c * (Module.basisUnique Unit hpfin).repr x PUnit.unit := by
        simpa using (congrArg
          (fun y : p => (Module.basisUnique Unit hpfin).repr y PUnit.unit) hc
          ).symm
      simp [LinearMap.toMatrix_apply, b, FiniteDimensional.basisSingleton_apply, hrepr,
        hxrepr_ne]
    rw [htrace_eq_c]
    exact hc_ne
  have htrace_comp :
      LinearMap.trace ℂ (LinearMap.BilinForm ℂ V) (flip.comp avg) =
        LinearMap.trace ℂ p flipP := by
    let inclFlip : p →ₗ[ℂ] LinearMap.BilinForm ℂ V := p.subtype.comp flipP
    have hfactor :
        flip.comp avg = inclFlip.comp avgToP := by
      ext x
      rfl
    have hcod : avgToP.comp p.subtype = LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact havgProj.codRestrict_apply_cod x
    rw [hfactor]
    calc
      LinearMap.trace ℂ (LinearMap.BilinForm ℂ V) (inclFlip.comp avgToP) =
        LinearMap.trace ℂ p (avgToP.comp inclFlip) := by
          simpa [LinearMap.comp_assoc] using
            (LinearMap.trace_comp_comm' (R := ℂ) (M := LinearMap.BilinForm ℂ V)
              (N := p) avgToP inclFlip)
      _ = LinearMap.trace ℂ p ((avgToP.comp p.subtype).comp flipP) := by
          rw [LinearMap.comp_assoc]
      _ = LinearMap.trace ℂ p (LinearMap.id.comp flipP) := by rw [hcod]
      _ = LinearMap.trace ℂ p flipP := by simp
  have havg_formula :
      LinearMap.trace ℂ (LinearMap.BilinForm ℂ V) (flip.comp avg) =
        ((Nat.card G : ℂ)⁻¹ * ∑ g : G, ρ.character g) := by
    calc
      LinearMap.trace ℂ (LinearMap.BilinForm ℂ V) (flip.comp avg) =
          LinearMap.trace ℂ (LinearMap.BilinForm ℂ V)
            (flip.comp (Representation.averageMap ρh)) := by
            rfl
      _ =
          ((Nat.card G : ℂ)⁻¹ * ∑ g : G, ρ.character (g⁻¹ * g⁻¹)) := by
            have hcomp_sum :
                flip.comp (∑ g : G, ρh g) = ∑ g : G, flip.comp (ρh g) := by
              ext x
              simp [LinearMap.comp_apply]
            have hcomp_smul :
                flip.comp (((Nat.card G : ℂ)⁻¹ : ℂ) • ∑ g : G, ρh g) =
                  (((Nat.card G : ℂ)⁻¹ : ℂ) • ∑ g : G, flip.comp (ρh g)) := by
              ext x
              simp [LinearMap.comp_apply]
            rw [Representation.averageMap, GroupAlgebra.average, map_smul, map_sum]
            simp [Representation.asAlgebraHom_def]
            rw [← Nat.card_eq_fintype_card]
            rw [hcomp_smul, map_smul, map_sum]
            congr 1
            refine Finset.sum_congr rfl ?_
            intro g hg
            exact representation_trace_flip_linHom_dual_eq_character_inv_mul_inv ρ g
      _ = ((Nat.card G : ℂ)⁻¹ * ∑ g : G, ρ.character g) := by
          rw [sum_classFunction_inv_mul_inv_eq_sum_of_odd_card hodd ρ.character]
  rw [← havg_formula, htrace_comp]
  exact htrace_flipP_ne

lemma trivialRepresentation_character_eq_principalCharacter
    {G : Type*} [Group G] [Finite G] :
    (Representation.trivial ℂ G ℂ).character = principalCharacter G := by
  ext g
  simp [Representation.character, Representation.trivial, principalCharacter]

set_option backward.isDefEq.respectTransparency false in
lemma trivialRepresentation_irreducible
    {G : Type*} [Group G] [Finite G] :
    Representation.IsIrreducible (Representation.trivial ℂ G ℂ) := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule, isSimpleModule_iff]
  exact is_simple_module_of_finrank_eq_one
    (K := ℂ) (A := MonoidAlgebra ℂ G)
    (V := (Representation.trivial ℂ G ℂ).asModule) (CommSemiring.finrank_self ℂ)

lemma representation_character_eq_principal_of_average_ne_zero
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V)
    (hρ_irreducible : Representation.IsIrreducible ρ)
    (havg : ((Nat.card G : ℂ)⁻¹ * ∑ g : G, ρ.character g) ≠ 0) :
    ρ.character = principalCharacter G := by
  classical
  let T : Representation ℂ G ℂ := Representation.trivial ℂ G ℂ
  have hTchar : T.character = principalCharacter G := by
    simpa [T] using trivialRepresentation_character_eq_principalCharacter (G := G)
  have hTirreducible : Representation.IsIrreducible T := by
    simpa [T] using trivialRepresentation_irreducible (G := G)
  have hcard_ne : (Nat.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩ : Nat.card G ≠ 0)
  letI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero hcard_ne
  have hhom :
      ((Nat.card G : ℂ)⁻¹ * ∑ g : G, ρ.character g =
        Module.finrank ℂ (Representation.IntertwiningMap T ρ)) := by
    simpa [hTchar, principalCharacter, mul_comm] using
      (Representation.card_inv_mul_sum_char_mul_char_eq_finrank (ρ := T) (σ := ρ))
  have hhom_ne : Module.finrank ℂ (Representation.IntertwiningMap T ρ) ≠ 0 := by
    intro hzero
    apply havg
    rw [hhom, hzero]
    simp
  have hexists : ∃ f : Representation.IntertwiningMap T ρ, f ≠ 0 := by
    by_contra hzero
    push Not at hzero
    have hsub : Subsingleton (Representation.IntertwiningMap T ρ) := by
      refine ⟨fun f g => ?_⟩
      rw [hzero f, hzero g]
    have hfinrank_zero : Module.finrank ℂ (Representation.IntertwiningMap T ρ) = 0 :=
      Module.finrank_zero_of_subsingleton
    exact hhom_ne hfinrank_zero
  rcases hexists with ⟨f, hf⟩
  letI : Representation.IsIrreducible T := hTirreducible
  letI : Representation.IsIrreducible ρ := hρ_irreducible
  have hbij : Function.Bijective f := by
    rcases Representation.IsIrreducible.bijective_or_eq_zero f with hbij | hzero
    · exact hbij
    · exact (hf hzero).elim
  let e : T.Equiv ρ := f.ofBijective hbij
  calc
    ρ.character = T.character := (Representation.char_iso e).symm
    _ = principalCharacter G := hTchar

theorem representation_proposition_1_1_brauer_count_node
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (hodd : Odd (Nat.card G)) (ρ : Representation ℂ G V)
    (hρ_irreducible : Representation.IsIrreducible ρ)
    (hfixed : ρ.character = conjugateCharacter ρ.character) :
    ρ.character = principalCharacter G := by
  exact representation_character_eq_principal_of_average_ne_zero ρ hρ_irreducible
    (representation_average_character_ne_zero_of_fixed_conjugate hodd ρ hρ_irreducible hfixed)

theorem proposition_1_1_brauer_count_node
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (hodd : Odd (Nat.card G)) :
    ∀ ρ : Representation ℂ G V,
      Representation.IsIrreducible ρ →
      ρ.character = conjugateCharacter ρ.character →
      ρ.character = principalCharacter G := by
  intro ρ hρ_irreducible hfixed
  exact representation_proposition_1_1_brauer_count_node hodd ρ hρ_irreducible hfixed

public theorem proposition_1_1
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (hodd : Odd (Nat.card G))
    (ρ : Representation ℂ G V) (hρ_irreducible : Representation.IsIrreducible ρ)
    (hne_principal : ρ.character ≠ principalCharacter G) :
    ρ.character ≠ conjugateCharacter ρ.character := by
  classical
  intro hfixed
  have hprincipal :
      ρ.character = principalCharacter G :=
    proposition_1_1_brauer_count_node hodd ρ hρ_irreducible hfixed
  exact hne_principal hprincipal

end CFSG.Section1
