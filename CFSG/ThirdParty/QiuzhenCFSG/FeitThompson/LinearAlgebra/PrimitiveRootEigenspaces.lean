module

public import Mathlib.Algebra.CharP.LinearMaps
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Semisimple
public import Mathlib.RepresentationTheory.Submodule
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.RingTheory.SimpleModule.Isotypic
public import Mathlib.RingTheory.ZMod.Torsion
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CriticalSubgroupLemmas
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Burnside.NormalComplement
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Extraspecial
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.LinearAlgebra.BlockElementaryMap
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ConjugateRep
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection2.EndFieldRep

namespace CFSG
end CFSG
open CFSG

open Representation
open Theory.Representation
open MonoidAlgebra
open Module
open Module.End
open Polynomial
open scoped DirectSum
open scoped BigOperators
open scoped TensorProduct
open scoped MonoidAlgebra
open scoped Function
/-
**Kind**: Theorem
**Note**: Proposition 2.4
**Stmt**:
Let $F$ be a field.
Let $V$ be a finite dimensional vector space over $F$, and $\dim V = q \ge 2$.
Let $g$ be an invertible linear transformation of $V$ of finite order $h \ge 2$.
Assume that $F$ contains a primitive $h$-th root of unity $\epsilon$.
For all integers $i$ and $t$ define:
- $E := \End_F(V)$.
- $V_i := \{v \in V | v g = \epsilon^i v\}$.
- $n_i := \dim V_i$.
- $E_i := \{e \in E | g^{-1} \epsilon g = \epsilon^i g\}$.
- $E_{i,t} := \{e \in E | V_i e \subseteq V_t, V_j e = 0, \forall j \ne i\}$.
Then
(a) $V = V_0 \oplus V_1 \oplus \cdots \oplus V_{h-1}$.
(b) $n_i = n_{i+h}$ for all $i$.
(c) $E = \bigoplus_{0 \le i,t \le h-1} E_{i,t}$.
(d) $\dim E_{i,t} = n_i n_t$ for all $i$ and $t$.
(e) $E_{i,t} \subseteq E_{t-i}$ for all $i$ and $t$.
(f) $E = \bigoplus_{t-i \equiv m (\mod h); 0 \le i,t \le h-1} E_{i,t}$ for all $m$.
(g) $\dim E_m = \sum_{i=0}^{h-1} n_i n_{i+m}$ for all $m$.
(h) $2\dim E_0 - 2\dim E_m = \sum_{i=0}^{h-1} (n_i - n_{i+m})^2$ for all $m$.
(j) If $\dim E_0 = \dim E_m + 1$ for all $m \not\equiv 0 (\mod h)$, then there exist integers $i, n$, and $\delta = \pm 1$ such that $q = hn + \delta, n_i = n + \delta$, and $n_j = n$ for all $j \not\equiv i (\mod h)$.
(k) Under the same assumptions as (j), $\dim V_0 = n_0 > 0$ unless $n = 1, i = 0, \delta = -1, h = q + 1$.
-/

/-- The submodule of endomorphisms intertwining `A` on the left with `B` on the right. -/
@[expose]
public def CFSG.intertwiningSubmodule
    {R : Type*} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M]
    (A B : End R M) :
  Submodule R (End R M) := {
    carrier := {X : End R M | A * X = X * B}
    add_mem' := by
      intro X Y hX hY
      simp_all only [Set.mem_setOf_eq]
      rw [mul_add, hX, hY, add_mul]
    zero_mem' := by simp only [Set.mem_setOf_eq, mul_zero, zero_mul]
    smul_mem' := by
      intro r X hX
      simp_all only [Set.mem_setOf_eq]
      rw [mul_smul_comm, hX, smul_mul_assoc]
  }

-- Lemma: injectivity of powers of a primitive root of unity
lemma CFSG.injective_powers {F : Type _} [Field F] {ε : F} {h : ℕ} (hε : IsPrimitiveRoot ε h) :
    Function.Injective (fun (i : Fin h) => ε ^ (i : ℤ)) := by
  intro i j hpow
  apply Fin.ext
  exact hε.pow_inj i.2 j.2 (by simpa using hpow)

-- Factorization lemmas (copied from nthRootsFinset_eq_powers2.lean)
lemma CFSG.mem_nthRootsFinset_iff {F : Type _} [Field F] {ε : F} {h : ℕ} (hε : IsPrimitiveRoot ε h) (hpos : 0 < h) (ζ : F) :
    ζ ∈ nthRootsFinset h (1 : F) ↔ ∃ i : Fin h, ζ = ε ^ (i : ℕ) := by
  classical
  haveI : NeZero h := ⟨hpos.ne'⟩
  constructor
  · intro hζ
    rw [mem_nthRootsFinset hpos] at hζ
    rcases hε.eq_pow_of_pow_eq_one hζ with ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    rw [mem_nthRootsFinset hpos]
    calc
      (ε ^ (i : ℕ)) ^ h = ε ^ ((i : ℕ) * h) := by rw [pow_mul]
      _ = (ε ^ h) ^ (i : ℕ) := by rw [mul_comm, pow_mul]
      _ = 1 ^ (i : ℕ) := by rw [hε.pow_eq_one]
      _ = 1 := by simp

open scoped Classical in
lemma CFSG.nthRootsFinset_eq_image {F : Type _} [Field F] {ε : F} {h : ℕ} (hε : IsPrimitiveRoot ε h) (hpos : 0 < h) :
    nthRootsFinset h (1 : F) = (Finset.univ : Finset (Fin h)).image (fun i : Fin h => ε ^ (i : ℕ)) := by
  classical
  haveI : NeZero h := ⟨hpos.ne'⟩
  ext ζ
  simp only [Finset.mem_image, Finset.mem_univ, true_and, mem_nthRootsFinset_iff hε hpos ζ, eq_comm]

lemma CFSG.prod_X_sub_powers_eq_X_pow_sub_one {F : Type _} [Field F] {ε : F} {h : ℕ} (hε : IsPrimitiveRoot ε h) (hpos : 0 < h) :
    ∏ i : Fin h, (X - C (ε ^ (i : ℤ))) = X ^ h - (1 : Polynomial F) := by
  classical
  calc
    ∏ i : Fin h, (X - C (ε ^ (i : ℤ))) = ∏ ζ ∈ ((Finset.univ : Finset (Fin h)).image (fun i : Fin h => ε ^ (i : ℤ))), (X - C ζ) := by
      have hinj : Set.InjOn (fun i : Fin h => ε ^ (i : ℤ)) (Finset.univ : Finset (Fin h)) := by
        intro i hi j hj hpow
        exact Fin.ext (hε.pow_inj i.2 j.2 (by simpa using hpow))
      rw [Finset.prod_image hinj]
    _ = ∏ ζ ∈ nthRootsFinset h (1 : F), (X - C ζ) := by rw [nthRootsFinset_eq_image hε hpos]; simp
    _ = X ^ h - (1 : Polynomial F) := by rw [Polynomial.X_pow_sub_one_eq_prod hpos hε]

public theorem CFSG.proposition_2_4_a
    {F : Type*} [Field F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {g : V ≃ₗ[F] V} {h : ℕ} (hg : g ^ h = 1) (hh : h ≥ 2)
    {ε : F} (hε : IsPrimitiveRoot ε h) :
    DirectSum.IsInternal <| fun (i : Fin h) => Module.End.eigenspace
    g.toLinearMap (ε ^ (i : ℤ)) := by
  -- Let f be the linear map associated to g
  let f : V →ₗ[F] V := g.toLinearMap
  have hpos : 0 < h := by omega
  -- f^h = 1
  have hf_pow : f ^ h = 1 := by
    ext v
    calc
      (f ^ h) v = ((g.toLinearMap) ^ h) v := rfl
      _ = ((LinearEquiv.automorphismGroup.toLinearMapMonoidHom g) ^ h) v := by simp
      _ = (LinearEquiv.automorphismGroup.toLinearMapMonoidHom (g ^ h)) v := by rw [MonoidHom.map_pow]
      _ = ((g ^ h).toLinearMap) v := by simp
      _ = ((1 : V ≃ₗ[F] V).toLinearMap) v := by rw [hg]
      _ = v := by simp
  have hf_aeval : aeval f (X ^ h - (1 : Polynomial F)) = 0 := by
    simp [hf_pow]
  -- X^h - 1 is separable (hence squarefree) because h ≠ 0 in F
  haveI : NeZero h := NeZero.of_pos hpos
  haveI : NeZero ((h : ℕ) : F) := IsPrimitiveRoot.neZero' hε
  have h_ne_zero : (h : F) ≠ 0 := NeZero.out
  have h_sep : (X ^ h - (1 : Polynomial F)).Separable := by
    rw [Polynomial.X_pow_sub_one_separable_iff]
    exact h_ne_zero
  have h_sqfree : Squarefree (X ^ h - (1 : Polynomial F)) := h_sep.squarefree
  -- Hence f is semisimple
  have h_semisimple : IsSemisimple f :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero h_sqfree hf_aeval
  -- Since V is finite-dimensional, f is finitely semisimple
  have h_finsemisimple : IsFinitelySemisimple f := by
    rw [Module.End.isFinitelySemisimple_iff_isSemisimple]
    exact h_semisimple
  -- Eigenvalues are h-th roots of unity
  have eigenvalue_root (μ : F) (hμ : HasEigenvalue f μ) : μ ^ h = 1 := by
    rcases hμ.exists_hasEigenvector with ⟨v, hv⟩
    have hv_ne : v ≠ 0 := (hasEigenvector_iff.mp hv).2
    have hpow := hv.pow_apply h
    have hf_pow_one : (f ^ h) v = v := by simp [hf_pow]
    have h_eq : μ ^ h • v = v := by rw [← hpow, hf_pow_one]
    have : (μ ^ h - 1) • v = 0 := by
      rw [sub_smul, h_eq, one_smul, sub_self]
    rcases smul_eq_zero.mp this with (hμh | hzero)
    · exact sub_eq_zero.mp hμh
    · exfalso
      exact hv_ne hzero
  -- Every eigenvalue μ is equal to ε ^ i for some i : Fin h
  have eigenvalue_is_power (μ : F) (hμ : HasEigenvalue f μ) : ∃ i : Fin h, μ = ε ^ i.val := by
    have hμ_pow : μ ^ h = 1 := eigenvalue_root μ hμ
    have hnz : NeZero h := NeZero.of_pos hpos
    rcases hε.eq_pow_of_pow_eq_one hμ_pow with ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩
  -- The family of eigenspaces indexed by eigenvalues is independent
  have h_indep_all : iSupIndep (eigenspace f) :=
    Module.End.eigenspaces_iSupIndep f
  -- The map i ↦ ε ^ i.val is injective
  have hinj : Function.Injective (fun i : Fin h => ε ^ (i : ℤ)) :=
    injective_powers hε
  -- Therefore the restricted family is also independent
  have h_indep : iSupIndep (fun i : Fin h => eigenspace f (ε ^ (i : ℤ))) :=
    h_indep_all.comp hinj
  -- Factorization of X^h - 1 into linear factors
  have h_factor : (X ^ h - (1 : Polynomial F)) = ∏ i : Fin h, (X - C (ε ^ (i : ℤ))) :=
    (prod_X_sub_powers_eq_X_pow_sub_one hε hpos).symm
  -- Pairwise coprimality of the linear factors
  have h_coprime : ∀ i j : Fin h, i ≠ j → IsCoprime (X - C (ε ^ (i : ℤ))) (X - C (ε ^ (j : ℤ))) := by
    intro i j hij
    apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
    have hne : ε ^ (i : ℕ) ≠ ε ^ (j : ℕ) := by
      intro h
      apply hij
      apply Fin.ext
      exact hε.pow_inj i.2 j.2 h
    simpa using (sub_ne_zero.mpr hne).isUnit
  -- Relate eigenspace to kernel of aeval (X - C μ)
  have eigenspace_eq_ker (μ : F) : eigenspace f μ = LinearMap.ker (aeval f (X - C μ)) := by
    simp [Module.End.eigenspace_def, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one]
  -- Show that the supremum of kernels equals kernel of product
  have h_sup_ker : ⨆ i : Fin h, LinearMap.ker (aeval f (X - C (ε ^ (i : ℤ)))) =
      LinearMap.ker (aeval f (∏ i : Fin h, (X - C (ε ^ (i : ℤ))))) := by
    classical
    have h_left : (⨆ i : Fin h, LinearMap.ker (aeval f (X - C (ε ^ (i : ℤ))))) =
        (Finset.univ : Finset (Fin h)).sup (fun i => LinearMap.ker (aeval f (X - C (ε ^ (i : ℤ))))) := by
      simp [Finset.sup_univ_eq_iSup]
    rw [h_left]
    have h_right : (∏ i ∈ (Finset.univ : Finset (Fin h)), (X - C (ε ^ (i : ℤ)))) = ∏ i : Fin h, (X - C (ε ^ (i : ℤ))) := by
      simp
    rw [h_right]
    refine Finset.induction_on (Finset.univ : Finset (Fin h)) ?_ ?_
    · simp [Finset.sup_empty, Finset.prod_empty, Polynomial.aeval_one, LinearMap.ker_id, Module.End.one_eq_id]
    · intro i s his ih
      rw [Finset.prod_insert his, Finset.sup_insert]
      have hcop : IsCoprime (∏ j ∈ s, (X - C (ε ^ (j : ℤ)))) (X - C (ε ^ (i : ℤ))) := by
        apply IsCoprime.prod_left
        intro j hj
        have hij' : i ≠ j := fun h => his (h ▸ hj)
        exact (h_coprime i j hij').symm
      rw [ih, sup_comm, Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime f hcop, mul_comm]
  -- The supremum of eigenspaces equals ⊤
  have h_sup : ⨆ i : Fin h, eigenspace f (ε ^ (i : ℤ)) = ⊤ := by
    calc
      ⨆ i : Fin h, eigenspace f (ε ^ (i : ℤ)) = ⨆ i : Fin h, LinearMap.ker (aeval f (X - C (ε ^ (i : ℤ)))) := by
        simp_rw [eigenspace_eq_ker]
      _ = LinearMap.ker (aeval f (∏ i : Fin h, (X - C (ε ^ (i : ℤ))))) := h_sup_ker
      _ = LinearMap.ker (aeval f (X ^ h - (1 : Polynomial F))) := by rw [h_factor]
      _ = LinearMap.ker (0 : V →ₗ[F] V) := by rw [hf_aeval]
      _ = (⊤ : Submodule F V) := by simp
  -- Now we have independence and spanning, so the family is internal
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  exact ⟨h_indep, h_sup⟩


-- Now we copy the lemmas from eigenspace_decomposition_v12 and projections_from_isInternal
public lemma LinearEquiv.toLinearMap_pow
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (e : M ≃ₗ[R] M) (n : ℕ) : (e ^ n).toLinearMap = e.toLinearMap ^ n := by
  induction n with
  | zero =>
      simp [LinearEquiv.coe_toLinearMap_one, pow_zero, Module.End.one_eq_id]
  | succ k ih =>
      calc
        (e ^ (k + 1)).toLinearMap = ((e ^ k) * e).toLinearMap := by rw [pow_succ]
        _ = (e ^ k).toLinearMap * e.toLinearMap := by rw [LinearEquiv.coe_toLinearMap_mul]
        _ = (e.toLinearMap ^ k) * e.toLinearMap := by rw [ih]
        _ = e.toLinearMap ^ (k + 1) := by rw [pow_succ]

-- Now we copy the lemmas from eigenspace_decomposition_v12 and projections_from_isInternal

-- Eigenspace decomposition theorem
theorem CFSG.eigenspace_decomposition {F : Type _} [Field F] {V : Type _} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {h : ℕ} (hh : h ≥ 2) (g : V ≃ₗ[F] V) (hg : g ^ h = 1) (ε : F) (hε : IsPrimitiveRoot ε h) :
    DirectSum.IsInternal (fun i : Fin h => eigenspace g.toLinearMap (ε ^ (i : ℤ))) := by
  -- local notation for the index set
  let I := Fin h
  -- define eigenspaces
  let E (i : I) : Submodule F V := eigenspace g.toLinearMap (ε ^ (i : ℤ))
  -- define node function
  let vals (ε : F) : I → F := fun i => ε ^ (i : ℕ)
  have vals_eq_zpow (i : I) : vals ε i = ε ^ (i : ℤ) := by
    simp [vals]
  have vals_injective : Set.InjOn (vals ε) ((Finset.univ : Finset I) : Set I) := by
    intro i hi j hj hij
    apply Fin.ext
    have hi' : (i : ℕ) < h := i.is_lt
    have hj' : (j : ℕ) < h := j.is_lt
    have hij' : ε ^ (i : ℕ) = ε ^ (j : ℕ) := by simpa [vals] using hij
    exact hε.pow_inj hi' hj' hij'
  have vals_injective_finset : ∀ i ∈ (Finset.univ : Finset I), ∀ j ∈ (Finset.univ : Finset I), vals ε i = vals ε j → i = j := by
    intro i hi j hj h
    exact vals_injective hi hj h
  have hpos : 0 < h := by linarith
  haveI : NeZero h := ⟨hpos.ne'⟩
  have hvals (i : I) : vals ε i ∈ nthRootsFinset h 1 := by
    have hpow : (vals ε i) ^ h = 1 := by
      dsimp [vals]
      calc
        (ε ^ (i : ℕ)) ^ h = ε ^ ((i : ℕ) * h) := by rw [pow_mul]
        _ = (ε ^ h) ^ (i : ℕ) := by rw [mul_comm, pow_mul]
        _ = 1 ^ (i : ℕ) := by rw [hε.pow_eq_one]
        _ = 1 := by simp
    simpa [mem_nthRootsFinset hpos (1 : F)] using hpow
  have surj : ∀ ζ ∈ nthRootsFinset h 1, ∃ i ∈ Finset.univ, vals ε i = ζ := by
    intro ζ hζ
    have hmem := (mem_nthRootsFinset hpos (1 : F)).mp hζ
    rcases hε.eq_pow_of_pow_eq_one hmem with ⟨i, hi, rfl⟩
    refine ⟨⟨i, hi⟩, Finset.mem_univ _, ?_⟩
    simp [vals]
  have nodal_eq_X_pow_sub_one : Lagrange.nodal (Finset.univ : Finset I) (vals ε) = X ^ h - 1 := by
    rw [Lagrange.nodal_eq, X_pow_sub_one_eq_prod hpos hε]
    refine Finset.prod_bij
      (f := fun i : I => X - C (vals ε i))
      (g := fun ζ : F => X - C ζ)
      (fun i _ => vals ε i)
      (fun i hi => hvals i)
      (fun i hi j hj h => vals_injective_finset i hi j hj h)
      (fun ζ hζ => ?_)
      (fun i hi => rfl)
    rcases surj ζ hζ with ⟨i, hi, rfl⟩
    exact ⟨i, hi, rfl⟩
  -- Lagrange basis polynomials
  let p (i : I) : F[X] := Lagrange.basis (Finset.univ : Finset I) (vals ε) i
  have eval_p_self (i : I) : (p i).eval (vals ε i) = 1 :=
    Lagrange.eval_basis_self vals_injective (Finset.mem_univ i)
  have eval_p_of_ne {i j : I} (hij : i ≠ j) : (p i).eval (vals ε j) = 0 :=
    Lagrange.eval_basis_of_ne hij (Finset.mem_univ j)
  haveI : Nonempty I := Fin.pos_iff_nonempty.mp hpos
  have sum_p : ∑ i ∈ (Finset.univ : Finset I), p i = 1 := by
    simpa using Lagrange.sum_basis vals_injective Finset.univ_nonempty
  have g_pow_eq_one_linearMap : (g.toLinearMap : Module.End F V) ^ h = 1 := by
    calc
      (g.toLinearMap : Module.End F V) ^ h = (g ^ h).toLinearMap := by
        rw [LinearEquiv.toLinearMap_pow]
      _ = (1 : V ≃ₗ[F] V).toLinearMap := by rw [hg]
      _ = (1 : Module.End F V) := by rfl
  have aeval_X_pow_sub_one_eq_zero : aeval (g.toLinearMap : Module.End F V) ((X : Polynomial F) ^ h - 1) = 0 := by
    calc
      aeval (g.toLinearMap : Module.End F V) ((X : Polynomial F) ^ h - 1) = (g.toLinearMap : Module.End F V) ^ h - 1 := by
        simp [Polynomial.aeval_sub, Polynomial.aeval_X_pow, Polynomial.aeval_one]
      _ = 0 := sub_eq_zero.mpr g_pow_eq_one_linearMap
  have h_eq (i : I) : (X - C (vals ε i)) * p i = C (Lagrange.nodalWeight (Finset.univ : Finset I) (vals ε) i) * (X ^ h - 1) := by
    set nodal := Lagrange.nodal (Finset.univ : Finset I) (vals ε)
    set w := Lagrange.nodalWeight (Finset.univ : Finset I) (vals ε) i
    have hweight_ne_zero : w ≠ 0 := Lagrange.nodalWeight_ne_zero vals_injective (Finset.mem_univ i)
    have h_dvd : X - C (vals ε i) ∣ nodal := Lagrange.X_sub_C_dvd_nodal (vals ε) (Finset.mem_univ i)
    have hmonic : Monic (X - C (vals ε i)) := monic_X_sub_C _
    have h_div_eq : (X - C (vals ε i)) * (nodal / (X - C (vals ε i))) = nodal := by
      rw [← Polynomial.divByMonic_eq_div _ hmonic,
          Polynomial.mul_divByMonic_eq_iff_isRoot.mpr]
      exact Polynomial.IsRoot.def.mpr (Lagrange.eval_nodal_at_node (Finset.mem_univ i))
    have h_basis_eq : Lagrange.basis (Finset.univ : Finset I) (vals ε) i = C w * (nodal / (X - C (vals ε i))) :=
      Lagrange.basis_eq_prod_sub_inv_mul_nodal_div (Finset.mem_univ i)
    calc
      (X - C (vals ε i)) * p i = (X - C (vals ε i)) * Lagrange.basis (Finset.univ : Finset I) (vals ε) i := rfl
      _ = (X - C (vals ε i)) * (C w * (nodal / (X - C (vals ε i)))) := by rw [h_basis_eq]
      _ = C w * ((X - C (vals ε i)) * (nodal / (X - C (vals ε i)))) := by ring
      _ = C w * nodal := by rw [h_div_eq]
      _ = C w * (X ^ h - 1) := by rw [nodal_eq_X_pow_sub_one]
  have hzero (i : I) : aeval (g.toLinearMap : Module.End F V) ((X - C (vals ε i)) * p i) = 0 := by
    rw [h_eq i]
    simp [Polynomial.aeval_mul, Polynomial.aeval_C, aeval_X_pow_sub_one_eq_zero]
  have basis_mul_X_sub_C_dvd_X_pow_sub_one (i : I) :
      (X - C (vals ε i)) * p i ∣ X ^ h - 1 := by
    have hweight_ne_zero : Lagrange.nodalWeight (Finset.univ : Finset I) (vals ε) i ≠ 0 :=
      Lagrange.nodalWeight_ne_zero vals_injective (Finset.mem_univ i)
    have hunit : IsUnit (C (Lagrange.nodalWeight (Finset.univ : Finset I) (vals ε) i)) :=
      Polynomial.isUnit_C.mpr (IsUnit.mk0 _ hweight_ne_zero)
    rw [h_eq i]
    exact (IsUnit.dvd_mul_left hunit).mp (dvd_refl _)
  let π (i : I) : Module.End F V := aeval g.toLinearMap (p i)
  have π_mapsTo (i : I) : ∀ v, π i v ∈ E i := by
    intro w
    dsimp [E]
    rw [mem_eigenspace_iff]
    have hzero := hzero i
    have Hcomp : (g.toLinearMap - (vals ε i) • (1 : Module.End F V)) ∘ₗ π i = aeval g.toLinearMap ((X - C (vals ε i)) * p i) := by
      calc
        (g.toLinearMap - vals ε i • (1 : Module.End F V)) ∘ₗ π i
            = (g.toLinearMap - vals ε i • (1 : Module.End F V)) * π i := by rw [Module.End.mul_eq_comp]
        _ = aeval g.toLinearMap ((X - C (vals ε i)) * p i) := by
          simp [π, p, Polynomial.aeval_mul, Polynomial.aeval_sub, Polynomial.aeval_X, Polynomial.aeval_C,
            Algebra.algebraMap_eq_smul_one]
    have H : (g.toLinearMap - (vals ε i) • (1 : Module.End F V)) ∘ₗ π i = 0 := by
      rw [Hcomp, hzero]
    have H' := LinearMap.congr_fun H w
    have Hsub : g.toLinearMap (π i w) - vals ε i • (π i w) = 0 := by
      simpa [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] using H'
    have Heq : g.toLinearMap (π i w) = vals ε i • (π i w) := by
      exact sub_eq_zero.mp Hsub
    rw [vals_eq_zpow i] at Heq
    exact Heq
  have sum_π_id : ∑ i ∈ Finset.univ, π i = 1 := by
    simp_rw [π, ← map_sum, sum_p, map_one]
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · -- independence
    have hinj : Function.Injective (vals ε) := by
      intro i j h
      exact vals_injective_finset i (Finset.mem_univ i) j (Finset.mem_univ j) h
    have := (Module.End.eigenspaces_iSupIndep g.toLinearMap).comp hinj
    simpa [Function.comp_def, vals_eq_zpow] using this
  · -- supremum equals top
    ext v
    simp_rw [Submodule.mem_iSup, Submodule.mem_top, iff_true]
    have hsum : v = ∑ i ∈ Finset.univ, π i v := by
      calc
        v = (1 : Module.End F V) v := by simp
        _ = (∑ i ∈ Finset.univ, π i) v := by rw [sum_π_id]
        _ = ∑ i ∈ Finset.univ, π i v := by simp [LinearMap.sum_apply]
    rw [hsum]
    intro N hN
    refine Submodule.sum_mem N fun i hi => ?_
    have hmem := π_mapsTo i v
    exact hN i hmem

section BlockEquality
variable {F : Type*} [Field F] {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {g : V ≃ₗ[F] V} {h : ℕ} (hge2 : h ≥ 2) (ε : F) (hε : IsPrimitiveRoot ε h)


open IsPrimitiveRoot
include hge2 hε

lemma CFSG.zpow_eq_zpow_iff_modEq' (a b : ℤ) : ε ^ a = ε ^ b ↔ a ≡ b [ZMOD h] := by
  have h_unit : IsUnit ε := hε.isUnit (by linarith)
  have horder : orderOf h_unit.unit = h := by
    calc
      orderOf h_unit.unit = orderOf (h_unit.unit : F) := (orderOf_units).symm
      _ = orderOf ε := by rw [h_unit.unit_spec]
      _ = h := hε.eq_orderOf.symm
  have H := zpow_eq_zpow_iff_modEq (x := h_unit.unit) (m := a) (n := b)
  have H' : ((h_unit.unit : F) ^ a = (h_unit.unit : F) ^ b) ↔ a ≡ b [ZMOD orderOf h_unit.unit] := by
    simpa [Units.ext_iff, Units.val_zpow_eq_zpow_val] using H
  simpa [h_unit.unit_spec, horder] using H'

omit [FiniteDimensional F V] in
lemma CFSG.eigenspace_eq_of_zpow_modEq (a b : ℤ) (hab : a ≡ b [ZMOD h]) :
    Module.End.eigenspace g.toLinearMap (ε ^ a) = Module.End.eigenspace g.toLinearMap (ε ^ b) := by
  have hpow : ε ^ a = ε ^ b := (zpow_eq_zpow_iff_modEq' hge2 ε hε a b).mpr hab
  rw [hpow]

end BlockEquality

-- Projections from an internal direct sum decomposition
public theorem CFSG.proposition_2_4_c
    {F : Type*} [Field F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {g : V ≃ₗ[F] V} {h : ℕ} (hg : g ^ h = 1) (hh : h ≥ 2)
    {ε : F} (hε : IsPrimitiveRoot ε h) :
    DirectSum.IsInternal (fun it : Fin h × Fin h =>
    blockElementaryMap (fun s : Fin h => eigenspace g.toLinearMap (ε ^ (s : ℤ))) it.1 it.2) :=
  isInternal_blockElementaryMap _ (eigenspace_decomposition hh g hg ε hε)

public theorem CFSG.proposition_2_4_d
    {F : Type*} [Field F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {g : V ≃ₗ[F] V} {h : ℕ} (hg : g ^ h = 1) (hh : h ≥ 2)
    {ε : F} (hε : IsPrimitiveRoot ε h) (i : ℤ) (t : ℤ) :
    Module.finrank F (blockElementaryMap (fun (s : Fin h) ↦ End.eigenspace g.toLinearMap (ε ^ (s : ℤ))) (@Fin.intCast h ⟨by omega⟩ i) (@Fin.intCast h ⟨by omega⟩ t)) =
    (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ (i : ℤ))) *
    (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ (t : ℤ))) := by
  let : NeZero h := by
    have hpos : 0 < h := by omega
    exact NeZero.of_pos hpos
  let ii : Fin h := @Fin.intCast h ⟨by omega⟩ i
  let tt : Fin h := @Fin.intCast h ⟨by omega⟩ t
  have hii :
      End.eigenspace g.toLinearMap (ε ^ ((ii : Fin h) : ℤ)) =
        End.eigenspace g.toLinearMap (ε ^ i) := by
    apply eigenspace_eq_of_zpow_modEq (hge2 := hh) (g := g) (h := h) (ε := ε) (hε := hε)
    have hval : ((ii : Fin h) : ℤ) = i % h := by
      have hnonneg : 0 ≤ i % h := by
        have hpos : 0 < h := by omega
        exact Int.emod_nonneg _ (Int.natCast_ne_zero.mpr (Nat.ne_of_gt hpos))
      have hcast :
          (((@Fin.intCast h (by infer_instance) i : Fin h).val : ℤ) : ℤ) = ((i % h).toNat : ℤ) :=
        congrArg (fun n : ℕ => (n : ℤ)) (Fin.val_intCast (n := h) i)
      simpa [ii, Int.toNat_of_nonneg hnonneg] using hcast
    simpa [hval] using (Int.mod_modEq i (h : ℤ))
  have htt :
      End.eigenspace g.toLinearMap (ε ^ ((tt : Fin h) : ℤ)) =
        End.eigenspace g.toLinearMap (ε ^ t) := by
    apply eigenspace_eq_of_zpow_modEq (hge2 := hh) (g := g) (h := h) (ε := ε) (hε := hε)
    have hval : ((tt : Fin h) : ℤ) = t % h := by
      have hnonneg : 0 ≤ t % h := by
        have hpos : 0 < h := by omega
        exact Int.emod_nonneg _ (Int.natCast_ne_zero.mpr (Nat.ne_of_gt hpos))
      have hcast :
          (((@Fin.intCast h (by infer_instance) t : Fin h).val : ℤ) : ℤ) = ((t % h).toNat : ℤ) :=
        congrArg (fun n : ℕ => (n : ℤ)) (Fin.val_intCast (n := h) t)
      simpa [tt, Int.toNat_of_nonneg hnonneg] using hcast
    simpa [hval] using (Int.mod_modEq t (h : ℤ))
  have hmain := blockElementaryMap_finrank
      (A := fun s : Fin h => End.eigenspace g.toLinearMap (ε ^ (s : ℤ)))
      (hA := eigenspace_decomposition hh g hg ε hε) ii tt
  rw [hii, htt] at hmain
  simpa [ii, tt] using hmain

public lemma CFSG.eigenspace_eq_intCast
    {F : Type*} [Field F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {g : V ≃ₗ[F] V} {h : ℕ} (hh : h ≥ 2)
    {ε : F} (hε : IsPrimitiveRoot ε h) (z : ℤ) :
    End.eigenspace g.toLinearMap (ε ^ ((@Fin.intCast h ⟨by omega⟩ z : Fin h) : ℤ)) =
      End.eigenspace g.toLinearMap (ε ^ z) := by
  letI : NeZero h := by
    exact NeZero.of_pos (by omega)
  have hnonneg : 0 ≤ z % h := by
    exact Int.emod_nonneg _ (Int.natCast_ne_zero.mpr (by omega))
  have hcast :
      (((@Fin.intCast h ‹_› z : Fin h).val : ℤ) : ℤ) = ((z % h).toNat : ℤ) :=
    congrArg (fun n : ℕ => (n : ℤ)) (Fin.val_intCast (n := h) z)
  have hval : ((@Fin.intCast h ‹_› z : Fin h) : ℤ) = z % h := by
    simpa [Int.toNat_of_nonneg hnonneg] using hcast
  apply eigenspace_eq_of_zpow_modEq (hge2 := hh) (g := g) (h := h) (ε := ε) (hε := hε)
  simpa [hval] using (Int.mod_modEq z (h : ℤ))

@[simp] lemma CFSG.fin_intCast_coe
    {h : ℕ} [NeZero h] (i : Fin h) :
    (@Fin.intCast h (by infer_instance) (i : ℤ)) = i := by
  apply Fin.ext
  have hnonneg : (0 : ℤ) ≤ (i : ℤ) := by
    exact_mod_cast Nat.zero_le i.1
  have hlt : (i : ℤ) < h := by
    exact_mod_cast i.2
  have hmod : ((i : ℤ) % h).toNat = i.1 := by
    rw [Int.emod_eq_of_lt hnonneg hlt]
    simp
  exact (Fin.val_intCast (n := h) (i : ℤ)).trans hmod

@[simp] lemma CFSG.fin_intCast_emod
    {h : ℕ} [NeZero h] (z : ℤ) :
    (@Fin.intCast h (by infer_instance) (z % h)) = @Fin.intCast h (by infer_instance) z := by
  have hnonneg : 0 ≤ z % h := by
    exact Int.emod_nonneg _ (Int.natCast_ne_zero.mpr (NeZero.ne h))
  have hval : ((@Fin.intCast h (by infer_instance) z : Fin h) : ℤ) = z % h := by
    have hcast :
        (((@Fin.intCast h (by infer_instance) z : Fin h).val : ℤ) : ℤ) = ((z % h).toNat : ℤ) :=
      congrArg (fun n : ℕ => (n : ℤ)) (Fin.val_intCast (n := h) z)
    simpa [Int.toNat_of_nonneg hnonneg] using hcast
  simpa [hval] using fin_intCast_coe (h := h) (i := (@Fin.intCast h (by infer_instance) z : Fin h))

lemma CFSG.fin_intCast_coe_int
    {h : ℕ} [NeZero h] (z : ℤ) :
    ((@Fin.intCast h (by infer_instance) z : Fin h) : ℤ) = z % h := by
  have hnonneg : 0 ≤ z % h := by
    exact Int.emod_nonneg _ (Int.natCast_ne_zero.mpr (NeZero.ne h))
  have hcast :
      (((@Fin.intCast h (by infer_instance) z : Fin h).val : ℕ) : ℤ) = ((z % h).toNat : ℤ) := by
    exact congrArg (fun n : ℕ => (n : ℤ)) (Fin.val_intCast (n := h) z)
  simpa [Int.toNat_of_nonneg hnonneg] using hcast

public theorem CFSG.proposition_2_4_e
    {F : Type*} [Field F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {g : V ≃ₗ[F] V} {h : ℕ} (hg : g ^ h = 1) (hh : h ≥ 2)
    {ε : F} (hε : IsPrimitiveRoot ε h) (i : ℤ) (t : ℤ) :
    (blockElementaryMap (fun (s : Fin h) ↦
    End.eigenspace g.toLinearMap (ε ^ (s : ℤ))) (@Fin.intCast h ⟨by omega⟩ i) (@Fin.intCast h ⟨by omega⟩ t)) ≤
    intertwiningSubmodule g.toLinearMap (ε ^ (t - i) • g.toLinearMap) := by
  letI : NeZero h := by
    exact NeZero.of_pos (by omega)
  let A : Fin h → Submodule F V := fun s ↦ End.eigenspace g.toLinearMap (ε ^ (s : ℤ))
  let hA : DirectSum.IsInternal A := eigenspace_decomposition hh g hg ε hε
  let ii : Fin h := @Fin.intCast h ‹_› i
  let tt : Fin h := @Fin.intCast h ‹_› t
  intro X hX
  rcases (mem_blockElementaryMap_iff A hA ii tt X).mp hX with ⟨hX1, hX2⟩
  have hii : A ii = End.eigenspace g.toLinearMap (ε ^ i) := by
    simpa [A, ii] using eigenspace_eq_intCast (hh := hh) (g := g) (h := h) (hε := hε) i
  have htt : A tt = End.eigenspace g.toLinearMap (ε ^ t) := by
    simpa [A, tt] using eigenspace_eq_intCast (hh := hh) (g := g) (h := h) (hε := hε) t
  have h_sup_top : ⨆ s : Fin h, A s = ⊤ := hA.submodule_iSup_eq_top
  have h_mem_sup (v : V) : v ∈ ⨆ s : Fin h, A s := by
    rw [h_sup_top]
    exact Submodule.mem_top
  refine LinearMap.ext fun v => ?_
  refine Submodule.iSup_induction (p := A)
    (motive := fun w => (g.toLinearMap * X) w = (X * (ε ^ (t - i) • g.toLinearMap)) w)
    (h_mem_sup v) ?_ (by simp) ?_
  · intro s w hw
    by_cases hsame : s = ii
    · rw [hsame] at hw
      have hwi : w ∈ End.eigenspace g.toLinearMap (ε ^ i) := by
        rwa [hii] at hw
      have hXt : X w ∈ End.eigenspace g.toLinearMap (ε ^ t) := by
        have hXt' : X w ∈ A tt := hX1 w hw
        rwa [htt] at hXt'
      have hgw : g.toLinearMap w = ε ^ i • w := (Module.End.mem_eigenspace_iff).mp hwi
      have hgXw : g.toLinearMap (X w) = ε ^ t • X w := (Module.End.mem_eigenspace_iff).mp hXt
      calc
        (g.toLinearMap * X) w = g.toLinearMap (X w) := by simp [Module.End.mul_apply]
        _ = ε ^ t • X w := hgXw
        _ = ε ^ ((t - i) + i) • X w := by rw [sub_add_cancel]
        _ = (ε ^ (t - i) * ε ^ i) • X w := by
          rw [zpow_add₀ (hε.ne_zero (by omega))]
        _ = ε ^ (t - i) • (ε ^ i • X w) := by rw [mul_smul]
        _ = ε ^ (t - i) • X (ε ^ i • w) := by rw [map_smul]
        _ = ε ^ (t - i) • X (g.toLinearMap w) := by rw [hgw]
        _ = (X * (ε ^ (t - i) • g.toLinearMap)) w := by
          simp [Module.End.mul_apply]
    · by_cases h_eq : A s = A ii
      · have h_bot : A ii = ⊥ := by
          exact submodule_eq_bot_of_eq_of_ne (A := A) (i := ii) (j := s) (h' := hA)
            (hij := by
              intro hsii
              exact hsame hsii.symm)
            (h_eq := h_eq.symm)
        have hwii : w ∈ A ii := by
          rwa [h_eq] at hw
        have hw0 : w = 0 := by
          rw [h_bot, Submodule.mem_bot] at hwii
          exact hwii
        simp [hw0, Module.End.mul_apply]
      · have hXw : X w = 0 := hX2 s h_eq w hw
        have hgw : g.toLinearMap w = ε ^ (s : ℤ) • w := by
          exact (Module.End.mem_eigenspace_iff).mp (by simpa [A] using hw)
        have hgw_mem : g.toLinearMap w ∈ A s := by
          rw [hgw]
          exact (A s).smul_mem (ε ^ (s : ℤ)) hw
        have hXgw : X (g.toLinearMap w) = 0 := hX2 s h_eq _ hgw_mem
        have hXgw' : X (g w) = 0 := by
          simpa using hXgw
        calc
          (g.toLinearMap * X) w = 0 := by
            simp [Module.End.mul_apply, hXw]
          _ = ε ^ (t - i) • X (g w) := by
            rw [hXgw', smul_zero]
          _ = (X * (ε ^ (t - i) • g.toLinearMap)) w := by
            simp [Module.End.mul_apply]
  · intro x y hx hy
    simp [Module.End.mul_apply, map_add, hx, hy]

public theorem CFSG.proposition_2_4_f
    {F : Type*} [Field F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {g : V ≃ₗ[F] V} {h : ℕ} (hg : g ^ h = 1) (hh : h ≥ 2)
    {ε : F} (hε : IsPrimitiveRoot ε h) (m : ℤ) :
    DirectSum.IsInternal <| fun (i : Fin h) ↦
    Submodule.comap (intertwiningSubmodule g.toLinearMap (ε ^ m • g.toLinearMap)).subtype
    (blockElementaryMap (fun (s : Fin h) ↦
    End.eigenspace g.toLinearMap (ε ^ (s : ℤ))) (@Fin.intCast h ⟨by omega⟩ i) (@Fin.intCast h ⟨by omega⟩ ((i + m) % h))) := by
  letI : NeZero h := by
    exact NeZero.of_pos (by omega)
  classical
  let A : Fin h → Submodule F V := fun s ↦ End.eigenspace g.toLinearMap (ε ^ (s : ℤ))
  let hA : DirectSum.IsInternal A := eigenspace_decomposition hh g hg ε hε
  let τ : Fin h → Fin h := fun i ↦ @Fin.intCast h ‹_› ((i : ℤ) + m)
  let B : Fin h → Submodule F (Module.End F V) := fun i ↦ blockElementaryMap A i (τ i)
  let N : Submodule F (Module.End F V) := intertwiningSubmodule g.toLinearMap (ε ^ m • g.toLinearMap)
  have hB_le : ∀ i : Fin h, B i ≤ N := by
    intro i
    have hsub : ((i : ℤ) + m) - (i : ℤ) = m := by
      omega
    simpa [A, B, N, τ, hsub] using
      proposition_2_4_e (hg := hg) (hh := hh) (hε := hε) (i := (i : ℤ)) (t := (i : ℤ) + m)
  have h_indep_all :
      iSupIndep (fun it : Fin h × Fin h ↦ blockElementaryMap A it.1 it.2) :=
    (proposition_2_4_c (hg := hg) (hh := hh) (hε := hε)).submodule_iSupIndep
  have hB_indep : iSupIndep B := by
    let f : Fin h → Fin h × Fin h := fun i ↦ (i, τ i)
    have hf : Function.Injective f := by
      intro i j hij
      exact congrArg Prod.fst hij
    simpa [B, f, Function.comp_def] using h_indep_all.comp hf
  have hX_map (X : Module.End F V) (hX : X ∈ N) (i : Fin h) {v : V} (hv : v ∈ A i) :
      X v ∈ A (τ i) := by
    have hXeq : g.toLinearMap * X = X * (ε ^ m • g.toLinearMap) := hX
    have hgv : g.toLinearMap v = ε ^ (i : ℤ) • v := by
      exact (Module.End.mem_eigenspace_iff).mp hv
    have hε0 : ε ≠ 0 := hε.ne_zero (by omega)
    have hcalc : g.toLinearMap (X v) = ε ^ ((i : ℤ) + m) • X v := by
      have htmp := congrArg (fun f : Module.End F V => f v) hXeq
      change (g.toLinearMap * X) v = (X * (ε ^ m • g.toLinearMap)) v at htmp
      rw [Module.End.mul_apply, Module.End.mul_apply, LinearMap.smul_apply, hgv] at htmp
      calc
        g.toLinearMap (X v) = X (ε ^ m • (ε ^ (i : ℤ) • v)) := by
          simpa [smul_smul] using htmp
        _ = X ((ε ^ m * ε ^ (i : ℤ)) • v) := by rw [smul_smul]
        _ = (ε ^ m * ε ^ (i : ℤ)) • X v := by rw [map_smul]
        _ = ε ^ ((i : ℤ) + m) • X v := by
          rw [← zpow_add₀ hε0, add_comm]
    have hmem : X v ∈ End.eigenspace g.toLinearMap (ε ^ ((i : ℤ) + m)) := by
      exact (Module.End.mem_eigenspace_iff).2 hcalc
    have hτ :
        A (τ i) = End.eigenspace g.toLinearMap (ε ^ ((i : ℤ) + m)) := by
      simpa [A, τ] using eigenspace_eq_intCast (hh := hh) (g := g) (h := h) (hε := hε) ((i : ℤ) + m)
    rw [hτ]
    exact hmem
  have hzero_t (X : Module.End F V) (hX : X ∈ N) (i t : Fin h) (ht : t ≠ τ i) :
      blockComponent A hA X i t = 0 := by
    ext v
    rw [blockComponent_apply, LinearMap.zero_apply]
    have hmem : X (projection A hA i v) ∈ A (τ i) :=
      hX_map X hX i (projection_maps_to A hA i v)
    exact projection_of_mem_ne A hA (τ i) t ht.symm _ hmem
  have hN_le : N ≤ ⨆ i : Fin h, B i := by
    intro X hX
    have hdecomp := decompose_endomorphism A hA X
    rw [hdecomp]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    have hsum :
        (∑ t : Fin h, blockComponent A hA X i t) = blockComponent A hA X i (τ i) := by
      refine Finset.sum_eq_single_of_mem (τ i) (Finset.mem_univ _) ?_
      intro t _ ht
      simp [hzero_t X hX i t ht]
    rw [hsum]
    exact Submodule.mem_iSup_of_mem i (blockComponent_mem_blockElementaryMap A hA X i (τ i))
  have h_eq : N = ⨆ i : Fin h, B i := by
    exact le_antisymm hN_le (iSup_le hB_le)
  let C : Fin h → Submodule F N := fun i ↦ Submodule.comap N.subtype (B i)
  have hC_indep : iSupIndep C := by
    let e : Submodule F N ≃o Set.Iic N := N.mapIic
    suffices (e ∘ C) = fun i ↦ ⟨B i, hB_le i⟩ by
      rw [← iSupIndep_map_orderIso_iff e, this]
      exact iSupIndep.of_coe_Iic_comp hB_indep
    funext i
    apply Subtype.ext
    ext x
    change x ∈ (C i).map N.subtype ↔ x ∈ B i
    rw [Submodule.map_comap_subtype, inf_of_le_right (hB_le i)]
  have hC_top : ⨆ i : Fin h, C i = ⊤ := by
    have hC_top' :
        ⨆ i : Fin h, Submodule.comap ((⨆ i ∈ (Set.univ : Set (Fin h)), B i)).subtype (B i) = ⊤ := by
      simpa using
        (Submodule.biSup_comap_subtype_eq_top (R := F) (M := Module.End F V)
          (s := (Set.univ : Set (Fin h))) (p := B))
    have h_eq' : (⨆ i ∈ (Set.univ : Set (Fin h)), B i) = N := by
      simp [h_eq]
    rw [h_eq'] at hC_top'
    simpa [C] using hC_top'
  have h_internal :
      DirectSum.IsInternal C := by
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    exact ⟨hC_indep, hC_top⟩
  simpa [A, C, B, N, τ, Int.emod_emod] using h_internal

public theorem CFSG.proposition_2_4_g
    {F : Type*} [Field F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {g : V ≃ₗ[F] V} {h : ℕ} (hg : g ^ h = 1) (hh : h ≥ 2)
    {ε : F} (hε : IsPrimitiveRoot ε h) (m : ℤ) :
    Module.finrank F (intertwiningSubmodule g.toLinearMap (ε ^ m • g.toLinearMap)) =
    ∑ i : Fin h,
    (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ i.val)) *
    (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ (i + m))) := by
  letI : NeZero h := by
    exact NeZero.of_pos (by omega)
  classical
  let A : Fin h → Submodule F V := fun s ↦ End.eigenspace g.toLinearMap (ε ^ (s : ℤ))
  let τ : Fin h → Fin h := fun i ↦ @Fin.intCast h ‹_› ((i : ℤ) + m)
  let B : Fin h → Submodule F (Module.End F V) := fun i ↦ blockElementaryMap A i (τ i)
  let N : Submodule F (Module.End F V) := intertwiningSubmodule g.toLinearMap (ε ^ m • g.toLinearMap)
  let C : Fin h → Submodule F N := fun i ↦ Submodule.comap N.subtype (B i)
  have hB_le : ∀ i : Fin h, B i ≤ N := by
    intro i
    have hsub : ((i : ℤ) + m) - (i : ℤ) = m := by
      omega
    simpa [A, B, N, τ, hsub] using
      proposition_2_4_e (hg := hg) (hh := hh) (hε := hε) (i := (i : ℤ)) (t := (i : ℤ) + m)
  have hC_internal :
      DirectSum.IsInternal C := by
    simpa [A, B, C, N, τ, Int.emod_emod] using
      proposition_2_4_f (hg := hg) (hh := hh) (hε := hε) m
  letI : ∀ i : Fin h, Module.Free F (C i) := fun i => Module.Free.of_divisionRing (K := F) (V := C i)
  letI : ∀ i : Fin h, Module.Finite F (C i) := fun i =>
    Module.Finite.of_basis (Module.finBasis F (C i))
  let e : (⨁ i : Fin h, C i) ≃ₗ[F] N := LinearEquiv.ofBijective (DirectSum.coeLinearMap C) hC_internal
  calc
    Module.finrank F N = Module.finrank F (⨁ i : Fin h, C i) := by
      rw [LinearEquiv.finrank_eq e]
    _ = ∑ i : Fin h, Module.finrank F (C i) := by simp
    _ = ∑ i : Fin h, Module.finrank F (B i) := by
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (hB_le i))]
    _ = ∑ i : Fin h,
        (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ (i : ℤ))) *
        (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ ((i : ℤ) + m))) := by
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      have hii : (@Fin.intCast h (by infer_instance) (i : ℤ)) = i := by simp
      have hdi :
          Module.finrank F (blockElementaryMap A (@Fin.intCast h (by infer_instance) (i : ℤ)) (τ i)) =
            (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ (i : ℤ))) *
            (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ ((i : ℤ) + m))) := by
        simpa [A, τ] using
          (proposition_2_4_d (hg := hg) (hh := hh) (hε := hε) (i := (i : ℤ)) (t := (i : ℤ) + m))
      rw [hii] at hdi
      simpa [B] using hdi
    _ = ∑ i : Fin h,
        (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ i.val)) *
        (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ (i + m))) := by
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [zpow_natCast]

public theorem CFSG.proposition_2_4_h
    {F : Type*} [Field F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {g : V ≃ₗ[F] V} {h : ℕ} (hg : g ^ h = 1) (hh : h ≥ 2)
    {ε : F} (hε : IsPrimitiveRoot ε h) (m : ℤ) :
    (2 : ℤ) * Module.finrank F (intertwiningSubmodule g.toLinearMap (ε ^ (0 : ℤ) • g.toLinearMap)) -
    (2 : ℤ) * Module.finrank F (intertwiningSubmodule g.toLinearMap (ε ^ m • g.toLinearMap)) =
    ∑ i : Fin h,
    (((Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ i.val) : ℤ) -
    (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ (i + m)) : ℤ)) ^ 2) := by
  letI : NeZero h := by
    exact NeZero.of_pos (by omega)
  let d : Fin h → ℤ := fun i ↦ Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ i.val)
  let s : Fin h := @Fin.intCast h ‹_› m
  let e : Fin h → ℤ := fun i ↦ d (s + i)
  have hzero (i : Fin h) :
      (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ ((i : ℤ) + 0)) : ℤ) = d i := by
    have hspace : End.eigenspace g.toLinearMap (ε ^ ((i : ℤ) + 0)) =
        End.eigenspace g.toLinearMap (ε ^ i.val) := by
      rw [add_zero, zpow_natCast]
    exact congrArg (fun W : Submodule F V => (Module.finrank F W : ℤ)) hspace
  have hshifti (i : Fin h) :
      (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ ((i : ℤ) + m)) : ℤ) = e i := by
    dsimp [e, d, s]
    have hmnonneg : 0 ≤ m % h := by
      exact Int.emod_nonneg _ (Int.natCast_ne_zero.mpr (NeZero.ne h))
    have hi_nonneg : 0 ≤ (i : ℤ) := by
      exact_mod_cast Nat.zero_le i.1
    have hi_lt : (i : ℤ) < h := by
      exact_mod_cast i.2
    have hmodi : (i : ℤ) % h = i := by
      rw [Int.emod_eq_of_lt hi_nonneg hi_lt]
    have hidx :
        (@Fin.intCast h ‹_› ((i : ℤ) + m) : Fin h) = @Fin.intCast h ‹_› m + i := by
      rw [Fin.ext_iff]
      have hz :
          (@Fin.intCast h ‹_› ((i : ℤ) + m) : Fin h).val = (((i : ℤ) + m) % h).toNat := by
        exact Fin.val_intCast (n := h) ((i : ℤ) + m)
      have hmval : (@Fin.intCast h ‹_› m : Fin h).val = (m % h).toNat := by
        exact Fin.val_intCast (n := h) m
      rw [hz, Fin.val_add, hmval]
      apply Int.natCast_inj.mp
      rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (Int.natCast_ne_zero.mpr (NeZero.ne h)))]
      rw [Int.natCast_mod, Int.natCast_add, Int.toNat_of_nonneg hmnonneg]
      rw [Int.add_emod, hmodi, add_comm]
    have hspace :
        End.eigenspace g.toLinearMap (ε ^ ((i : ℤ) + m)) =
          End.eigenspace g.toLinearMap (ε ^ ((@Fin.intCast h ‹_› m + i : Fin h) : ℤ)) := by
      simpa [hidx] using
        (eigenspace_eq_intCast (hh := hh) (g := g) (h := h) (hε := hε) ((i : ℤ) + m)).symm
    have hspace' : End.eigenspace g.toLinearMap (ε ^ ((i : ℤ) + m)) =
        End.eigenspace g.toLinearMap (ε ^ ((@Fin.intCast h ‹_› m + i : Fin h).val)) := by
      simpa [zpow_natCast] using hspace
    exact congrArg (fun W : Submodule F V => (Module.finrank F W : ℤ)) hspace'
  have h0 :
      (Module.finrank F (intertwiningSubmodule g.toLinearMap (ε ^ (0 : ℤ) • g.toLinearMap)) : ℤ) =
        ∑ i : Fin h, d i * d i := by
    rw [proposition_2_4_g (hg := hg) (hh := hh) (hε := hε) (m := 0)]
    push_cast
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [hzero i]
  have hm :
      (Module.finrank F (intertwiningSubmodule g.toLinearMap (ε ^ m • g.toLinearMap)) : ℤ) =
        ∑ i : Fin h, d i * e i := by
    rw [proposition_2_4_g (hg := hg) (hh := hh) (hε := hε) (m := m)]
    push_cast
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [hshifti i]
  have hshift :
      ∑ i : Fin h, e i * e i = ∑ i : Fin h, d i * d i := by
    simpa [e, add_assoc, add_comm, pow_two] using
      (Fintype.sum_bijective (fun i : Fin h ↦ s + i) (AddGroup.addLeft_bijective s)
        (fun i : Fin h ↦ d (s + i) * d (s + i)) (fun i : Fin h ↦ d i * d i) (fun i ↦ rfl))
  have hsq :
      ∑ i : Fin h, (d i - e i) ^ 2 =
        (∑ i : Fin h, d i * d i) + (∑ i : Fin h, e i * e i) - 2 * ∑ i : Fin h, d i * e i := by
    simp_rw [sub_sq', pow_two]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
  calc
    (2 : ℤ) * Module.finrank F (intertwiningSubmodule g.toLinearMap (ε ^ (0 : ℤ) • g.toLinearMap)) -
        (2 : ℤ) * Module.finrank F (intertwiningSubmodule g.toLinearMap (ε ^ m • g.toLinearMap)) =
      2 * (∑ i : Fin h, d i * d i) - 2 * (∑ i : Fin h, d i * e i) := by
        rw [h0, hm]
    _ = (∑ i : Fin h, d i * d i) + (∑ i : Fin h, e i * e i) - 2 * ∑ i : Fin h, d i * e i := by
      rw [hshift]
      ring_nf
    _ = ∑ i : Fin h, (d i - e i) ^ 2 := by
      exact hsq.symm
    _ = ∑ i : Fin h,
        (((Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ i.val) : ℤ) -
        (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ (i + m)) : ℤ)) ^ 2) := by
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      rw [← hshifti i]

public theorem CFSG.proposition_2_4_j
    {F : Type*} [Field F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {q : ℕ} (hdim : Module.finrank F V = q)
    {g : V ≃ₗ[F] V} {h : ℕ} (hg : g ^ h = 1) (hh : h ≥ 2)
    {ε : F} (hε : IsPrimitiveRoot ε h)
    (hE : ∀ m : ℤ, ¬ (m % h = 0) →
      Module.finrank F (intertwiningSubmodule g.toLinearMap (ε ^ (0 : ℤ) • g.toLinearMap)) =
      Module.finrank F (intertwiningSubmodule g.toLinearMap (ε ^ m • g.toLinearMap)) + 1) :
    ∃ i : ℤ, ∃ n : ℤ, ∃ δ : ℤ, (δ = 1 ∨ δ = -1) ∧ q = h * n + δ ∧
    (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ i)) = n + δ ∧
    ∀ j : ℤ, ¬ ((j - i) % h) = 0 →
    (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ j)) = n := by
  classical
  letI : NeZero h := by
    exact NeZero.of_pos (by omega)
  let d : Fin h -> Int := fun i => Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ (i : Int))
  let s1 : Fin h -> Fin h := fun i => @Fin.intCast h (by infer_instance) ((i : Int) + 1)
  let s2 : Fin h -> Fin h := fun i => @Fin.intCast h (by infer_instance) ((i : Int) + 2)
  let a1 : Fin h -> Int := fun i => (d i - d (s1 i)) ^ 2
  let a2 : Fin h -> Int := fun i => (d i - d (s2 i)) ^ 2
  have hshift (m : Int) (i : Fin h) :
      (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ ((i : Int) + m)) : Int) =
        d (@Fin.intCast h (by infer_instance) ((i : Int) + m)) := by
    have hspace :
        End.eigenspace g.toLinearMap (ε ^ ((@Fin.intCast h (by infer_instance) ((i : Int) + m) : Fin h) : Int)) =
          End.eigenspace g.toLinearMap (ε ^ ((i : Int) + m)) := by
      simpa using
        eigenspace_eq_intCast (hh := hh) (g := g) (h := h) (hε := hε) ((i : Int) + m)
    calc
      (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ ((i : Int) + m)) : Int) =
          (Module.finrank F <| End.eigenspace g.toLinearMap
            (ε ^ ((@Fin.intCast h (by infer_instance) ((i : Int) + m) : Fin h) : Int)) : Int) := by
              exact congrArg (fun W : Submodule F V => (Module.finrank F W : Int)) hspace.symm
      _ = d (@Fin.intCast h (by infer_instance) ((i : Int) + m)) := by
            simp [d]
  let c0 : Int :=
    Module.finrank F (intertwiningSubmodule g.toLinearMap (ε ^ (0 : Int) • g.toLinearMap))
  let c1 : Int :=
    Module.finrank F (intertwiningSubmodule g.toLinearMap (ε ^ (1 : Int) • g.toLinearMap))
  have h1mod : ¬ ((1 : Int) % h = 0) := by
    intro hmod
    have hdvd : (h : Int) ∣ 1 := Int.dvd_iff_emod_eq_zero.mpr hmod
    have hle : (h : Int) ≤ 1 := Int.le_of_dvd (by norm_num) hdvd
    omega
  have hE1 : c0 = c1 + 1 := by
    dsimp [c0, c1]
    exact_mod_cast hE 1 h1mod
  have hsum1_raw := proposition_2_4_h (hg := hg) (hh := hh) (hε := hε) (m := 1)
  have hsum1_left : (2 : Int) * c0 - (2 : Int) * c1 = 2 := by
    omega
  have hcast_rank (z : Int) :
      (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ z) : Int) =
        d (@Fin.intCast h (by infer_instance) z) := by
    simpa [d] using
      congrArg (fun W : Submodule F V => (Module.finrank F W : Int))
        (eigenspace_eq_intCast (hh := hh) (g := g) (h := h) (hε := hε) z).symm
  have hsum1' :
      (∑ i : Fin h,
        (((Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ (i : ℕ)) : Int) -
          (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ ((i : Int) + 1)) : Int)) ^ 2)) = 2 := by
    calc
      (∑ i : Fin h,
        (((Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ (i : ℕ)) : Int) -
          (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ ((i : Int) + 1)) : Int)) ^ 2))
          = (2 : Int) * c0 - (2 : Int) * c1 := by
        simpa [c0, c1] using hsum1_raw.symm
      _ = 2 := hsum1_left
  have hsum1 : (∑ i : Fin h, a1 i) = 2 := by
    have hsum1a :
        ∑ i : Fin h, a1 i =
          ∑ i : Fin h,
            ((d i -
              (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ ((i : Int) + 1)) : Int)) ^ 2) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      dsimp [a1, s1]
      rw [← hshift 1 i]
    have hsum1b :
        (∑ i : Fin h,
          ((d i -
            (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ ((i : Int) + 1)) : Int)) ^ 2)) =
          ∑ i : Fin h,
            (((Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ (i : ℕ)) : Int) -
              (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ ((i : Int) + 1)) : Int)) ^ 2) := by
      refine Finset.sum_congr rfl fun i hi => ?_
      change (((Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ ((i : Int))) : Int) -
          (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ ((i : Int) + 1)) : Int)) ^ 2) =
        (((Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ (i : ℕ)) : Int) -
          (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ ((i : Int) + 1)) : Int)) ^ 2)
      rw [zpow_natCast]
    calc
      ∑ i : Fin h, a1 i =
          ∑ i : Fin h,
            ((d i -
              (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ ((i : Int) + 1)) : Int)) ^ 2) := hsum1a
      _ =
          ∑ i : Fin h,
            (((Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ (i : ℕ)) : Int) -
              (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ ((i : Int) + 1)) : Int)) ^ 2) := hsum1b
      _ = 2 := hsum1'
  let A : Fin h -> Submodule F V := fun i => End.eigenspace g.toLinearMap (ε ^ (i : Int))
  have hqsum_nat_A :
      Module.finrank F V = ∑ i : Fin h, Module.finrank F (A i) := by
    letI : ∀ i : Fin h, Module.Free F (A i) := fun i =>
      Module.Free.of_divisionRing (K := F) (V := A i)
    letI : ∀ i : Fin h, Module.Finite F (A i) := fun i =>
      Module.Finite.of_basis (Module.finBasis F (A i))
    let e : (⨁ i : Fin h, A i) ≃ₗ[F] V :=
      LinearEquiv.ofBijective (DirectSum.coeLinearMap A) (eigenspace_decomposition hh g hg ε hε)
    calc
      Module.finrank F V = Module.finrank F (⨁ i : Fin h, A i) := by
        rw [LinearEquiv.finrank_eq e]
      _ = ∑ i : Fin h, Module.finrank F (A i) := by
        simp
  have hqsum_nat :
      Module.finrank F V =
        ∑ i : Fin h, Module.finrank F (End.eigenspace g.toLinearMap (ε ^ (i : Int))) := by
    simpa [A] using hqsum_nat_A
  have hqsum : (q : ℤ) = ∑ i : Fin h, d i := by
    rw [← hdim]
    calc
      (Module.finrank F V : ℤ) =
          ((∑ i : Fin h, Module.finrank F (End.eigenspace g.toLinearMap (ε ^ (i : ℤ)))) : ℤ) := by
            exact_mod_cast hqsum_nat
      _ = ∑ i : Fin h, d i := by
            simp [d]
  let S2 : Finset (Fin h) := Finset.univ.filter fun i => d i ≠ d 0
  have hS2ne : S2.Nonempty := by
    by_contra hEmpty
    have hconst0 : ∀ i : Fin h, d i = d 0 := by
      intro i
      by_contra hi
      exact hEmpty ⟨i, by simp [S2, hi]⟩
    have hsum1_zero : ∑ i : Fin h, a1 i = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      dsimp [a1]
      rw [hconst0 i, hconst0 (s1 i)]
      ring
    omega
  let j : Fin h := S2.min' hS2ne
  let k : Fin h := S2.max' hS2ne
  have hj_mem : j ∈ S2 := by
    exact Finset.min'_mem S2 hS2ne
  have hk_mem : k ∈ S2 := by
    exact Finset.max'_mem S2 hS2ne
  have h0_not_mem : (0 : Fin h) ∉ S2 := by
    simp [S2]
  have hj_ne_zero : j ≠ 0 := by
    intro hj0
    exact h0_not_mem (hj0 ▸ hj_mem)
  have hj_pos : 0 < j.val := by
    exact Nat.pos_of_ne_zero (by
      intro h0
      exact hj_ne_zero (Fin.ext h0))
  have hj_le_k : j ≤ k := by
    exact Finset.min'_le S2 k hk_mem
  let jm1 : Fin h := ⟨j.val - 1, by omega⟩
  have hjm1_lt_j : jm1 < j := by
    rw [Fin.lt_def]
    dsimp [jm1]
    omega
  have hs1_jm1 : s1 jm1 = j := by
    have hidx : ((jm1 : ℤ) + 1) = (j : ℤ) := by
      dsimp [jm1]
      omega
    dsimp [s1]
    rw [hidx]
    simp
  have hjm1_not_mem : jm1 ∉ S2 := by
    intro hjm1_mem
    exact (not_le_of_gt hjm1_lt_j) (Finset.min'_le S2 jm1 hjm1_mem)
  have houtside_eq0 (t : Fin h) (ht : t < j ∨ k < t) : d t = d 0 := by
    by_cases htmem : t ∈ S2
    · exfalso
      cases ht with
      | inl htlt =>
          exact (not_le_of_gt htlt) (Finset.min'_le S2 t htmem)
      | inr hkt =>
          exact (not_le_of_gt hkt) (Finset.le_max' S2 t htmem)
    · by_contra hneq
      exact htmem (by simp [S2, hneq])
  have hd_j_ne : d j ≠ d 0 := by
    simpa [S2] using hj_mem
  have hd_k_ne : d k ≠ d 0 := by
    simpa [S2] using hk_mem
  have hd_jm1 : d jm1 = d 0 := by
    exact houtside_eq0 jm1 (Or.inl hjm1_lt_j)
  have hs1k_eq0_or_gt : s1 k = 0 ∨ k < s1 k := by
    by_cases hk1 : k.val + 1 < h
    · right
      have hs1k :
          s1 k = (⟨k.val + 1, hk1⟩ : Fin h) := by
        simpa [s1] using
          (fin_intCast_coe (h := h) (i := (⟨k.val + 1, hk1⟩ : Fin h)))
      rw [hs1k, Fin.lt_def]
      simp
    · left
      have hkval : k.val = h - 1 := by
        omega
      have hk_cast : (k : Int) = ((h - 1 : Nat) : Int) := by
        exact_mod_cast hkval
      have hk1eq : (k : Int) + 1 = h := by
        omega
      apply Fin.ext
      change (((((k : Int) + 1) % h).toNat) = ((0 : Fin h).val))
      have hmod : (((k : Int) + 1) % h) = 0 := by
        rw [hk1eq]
        exact Int.emod_eq_zero_of_dvd (show (h : Int) ∣ h by exact dvd_rfl)
      simp [hmod]
  have hd_s1k : d (s1 k) = d 0 := by
    cases hs1k_eq0_or_gt with
    | inl hs1k0 =>
        rw [hs1k0]
    | inr hks1k =>
        exact houtside_eq0 (s1 k) (Or.inr hks1k)
  have ha1_jm1_pos : 0 < a1 jm1 := by
    have hne : d jm1 - d (s1 jm1) ≠ 0 := by
      rw [hd_jm1, hs1_jm1]
      exact sub_ne_zero.mpr (Ne.symm hd_j_ne)
    simpa [a1] using sq_pos_iff.mpr hne
  have ha1_k_pos : 0 < a1 k := by
    have hne : d k - d (s1 k) ≠ 0 := by
      rw [hd_s1k]
      exact sub_ne_zero.mpr hd_k_ne
    simpa [a1] using sq_pos_iff.mpr hne
  have hjm1_lt_k : jm1 < k := lt_of_lt_of_le hjm1_lt_j hj_le_k
  have hjm1_ne_k : jm1 ≠ k := ne_of_lt hjm1_lt_k
  let R1 : Finset (Fin h) := ((Finset.univ.erase jm1).erase k)
  have hsum1_decomp :
      ∑ i : Fin h, a1 i = a1 jm1 + a1 k + ∑ i ∈ R1, a1 i := by
    rw [← Finset.add_sum_erase Finset.univ (fun i : Fin h => a1 i) (Finset.mem_univ jm1)]
    have hk_mem' : k ∈ Finset.univ.erase jm1 := by
      exact Finset.mem_erase.mpr ⟨fun hEq => hjm1_ne_k hEq.symm, Finset.mem_univ k⟩
    rw [← Finset.add_sum_erase (Finset.univ.erase jm1) (fun i : Fin h => a1 i) hk_mem']
    change a1 jm1 + (a1 k + ∑ i ∈ R1, a1 i) = a1 jm1 + a1 k + ∑ i ∈ R1, a1 i
    rw [add_assoc]
  have hR1_nonneg : 0 ≤ ∑ i ∈ R1, a1 i := by
    exact Finset.sum_nonneg fun i hi => by
      dsimp [a1]
      exact sq_nonneg _
  have hR1_eq_zero : ∑ i ∈ R1, a1 i = 0 := by
    have h1 : 1 ≤ a1 jm1 := by
      omega
    have h2 : 1 ≤ a1 k := by
      omega
    omega
  have ha1_eq_zero {i : Fin h} (hi1 : i ≠ jm1) (hi2 : i ≠ k) : a1 i = 0 := by
    have hi : i ∈ R1 := by
      simp [R1, hi1, hi2]
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => by
      dsimp [a1]
      exact sq_nonneg _)).mp hR1_eq_zero i hi
  have hs1_idx (m : ℕ) (hm : j.val + m + 1 < h) :
      s1 (⟨j.val + m, by omega⟩ : Fin h) = (⟨j.val + (m + 1), by omega⟩ : Fin h) := by
    have harg :
        ((⟨j.val + m, by omega⟩ : Fin h) : Int) + 1 =
          ((⟨j.val + (m + 1), hm⟩ : Fin h) : Int) := by
      simp
      omega
    change @Fin.intCast h (by infer_instance)
      (((⟨j.val + m, by omega⟩ : Fin h) : Int) + 1) =
        (⟨j.val + (m + 1), hm⟩ : Fin h)
    rw [harg]
    exact fin_intCast_coe (h := h) (i := (⟨j.val + (m + 1), hm⟩ : Fin h))
  have hblock_const_nat :
      ∀ m : ℕ, ∀ hm : m ≤ k.val - j.val,
        d (⟨j.val + m, by omega⟩ : Fin h) = d j := by
    intro m hm
    induction m with
    | zero =>
        have hidx : (⟨j.val, by omega⟩ : Fin h) = j := by
          apply Fin.ext
          simp
        simp
    | succ m ih =>
        have hm_lt : m < k.val - j.val := Nat.lt_of_succ_le hm
        have hzero :
            a1 (⟨j.val + m, by omega⟩ : Fin h) = 0 := by
          apply ha1_eq_zero
          · intro hEq
            have hvals : j.val + m = j.val - 1 := by
              simpa [jm1] using congrArg Fin.val hEq
            omega
          · intro hEq
            have hvals : j.val + m = k.val := by
              simpa using congrArg Fin.val hEq
            omega
        have hstep :
            d (⟨j.val + m, by omega⟩ : Fin h) =
              d (s1 (⟨j.val + m, by omega⟩ : Fin h)) := by
          have hsub :
              d (⟨j.val + m, by omega⟩ : Fin h) -
                d (s1 (⟨j.val + m, by omega⟩ : Fin h)) = 0 := by
            exact sq_eq_zero_iff.mp hzero
          exact sub_eq_zero.mp hsub
        have hs1eq :
            s1 (⟨j.val + m, by omega⟩ : Fin h) = (⟨j.val + (m + 1), by omega⟩ : Fin h) := by
          exact hs1_idx m (by omega)
        calc
          d (⟨j.val + (m + 1), by omega⟩ : Fin h)
              = d (s1 (⟨j.val + m, by omega⟩ : Fin h)) := by
                rw [hs1eq]
          _ = d (⟨j.val + m, by omega⟩ : Fin h) := hstep.symm
          _ = d j := ih (Nat.le_of_lt hm_lt)
  have hinside_const (t : Fin h) (hjt : j ≤ t) (htk : t ≤ k) : d t = d j := by
    have hrepr : t = (⟨j.val + (t.val - j.val), by omega⟩ : Fin h) := by
      apply Fin.ext
      have hjt' : j.val ≤ t.val := hjt
      simpa [add_comm] using (Nat.sub_add_cancel hjt').symm
    rw [hrepr]
    exact hblock_const_nat (t.val - j.val) (by omega)
  have hd_k_eq : d k = d j := by
    exact hinside_const k hj_le_k le_rfl
  have ha1_k_eq_jm1 : a1 k = a1 jm1 := by
    dsimp [a1]
    rw [hd_k_eq, hd_s1k, hd_jm1, hs1_jm1]
    ring
  have ha1_jm1_eq_one : a1 jm1 = 1 := by
    omega
  have hdelta : d j - d 0 = 1 ∨ d j - d 0 = -1 := by
    have hsq : (d j - d 0) ^ 2 = 1 := by
      calc
        (d j - d 0) ^ 2 = a1 jm1 := by
          dsimp [a1]
          rw [hd_jm1, hs1_jm1]
          ring
        _ = 1 := ha1_jm1_eq_one
    exact sq_eq_one_iff.mp hsq
  have hcast_eq_mod_zero {z : Int} {t : Fin h} (ht : @Fin.intCast h (by infer_instance) z = t) :
      ((z - (t : Int)) % h) = 0 := by
    have hzmod : z % h = (t : Int) := by
      calc
        z % h = ((@Fin.intCast h (by infer_instance) z : Fin h) : Int) := by
          symm
          exact fin_intCast_coe_int (h := h) (z := z)
        _ = t := by simp [ht]
    have htmod : ((t : Int) % h) = (t : Int) := by
      calc
        ((t : Int) % h) = ((@Fin.intCast h (by infer_instance) (t : Int) : Fin h) : Int) := by
          symm
          exact fin_intCast_coe_int (h := h) (z := (t : Int))
        _ = t := by simp
    have hmodEq : z ≡ (t : Int) [ZMOD h] := by
      show z % h = ((t : Int) % h)
      rw [hzmod, htmod]
    have hdvd : (h : Int) ∣ ((t : Int) - z) := Int.modEq_iff_dvd.mp hmodEq
    have hdvd' : (h : Int) ∣ (z - (t : Int)) := by
      have hneg : (h : Int) ∣ -((t : Int) - z) := Int.dvd_neg.mpr hdvd
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hneg
    exact Int.dvd_iff_emod_eq_zero.mp hdvd'
  by_cases hjk : j = k
  · have houtside_j {t : Fin h} (ht : t ≠ j) : d t = d 0 := by
      rcases lt_or_gt_of_ne ht with hlt | hgt
      · exact houtside_eq0 t (Or.inl hlt)
      · exact houtside_eq0 t (Or.inr (by simpa [hjk] using hgt))
    have hsum_rest :
        ∑ t ∈ Finset.univ.erase j, d t = ∑ t ∈ Finset.univ.erase j, d 0 := by
      refine Finset.sum_congr rfl fun t ht => ?_
      exact houtside_j (Finset.mem_erase.mp ht).1
    have hqeq : (q : Int) = h * d 0 + (d j - d 0) := by
      calc
        (q : Int) = ∑ t : Fin h, d t := hqsum
        _ = d j + ∑ t ∈ Finset.univ.erase j, d t := by
              symm
              exact Finset.add_sum_erase Finset.univ (fun t : Fin h => d t) (Finset.mem_univ j)
        _ = d j + ∑ t ∈ Finset.univ.erase j, d 0 := by rw [hsum_rest]
        _ = d j + ((h - 1 : Nat) : Int) * d 0 := by simp
        _ = d j + (h - 1) * d 0 := by
              have h1 : 1 ≤ h := by omega
              rw [Nat.cast_sub h1]
              norm_num
        _ = h * d 0 + (d j - d 0) := by ring
    refine ⟨(j : Int), d 0, d j - d 0, hdelta, ?_, ?_, ?_⟩
    · simpa using hqeq
    · calc
        (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ (j : Int)) : Int) = d j := by
          simpa using hcast_rank (j : Int)
        _ = d 0 + (d j - d 0) := by omega
    · intro z hz
      have ht_ne : @Fin.intCast h (by infer_instance) z ≠ j := by
        intro hEq
        exact hz (hcast_eq_mod_zero (t := j) hEq)
      calc
        (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ z) : Int) =
            d (@Fin.intCast h (by infer_instance) z) := hcast_rank z
        _ = d 0 := houtside_j ht_ne
  · by_cases hcomp : j = 1 ∧ k.val = h - 1
    · have hj1 : j = 1 := hcomp.1
      have hk_last : k.val = h - 1 := hcomp.2
      have hdelta0 : d 0 - d j = 1 ∨ d 0 - d j = -1 := by
        cases hdelta with
        | inl hdelta1 =>
            right
            omega
        | inr hdelta1 =>
            left
            omega
      have hinside_nonzero {t : Fin h} (ht0 : t ≠ 0) : d t = d j := by
        have hjt : j ≤ t := by
          have hjvalmod : j.val = 1 % h := by
            simpa using congrArg Fin.val hj1
          have hjval : j.val = 1 := by
            have hlt : 1 < h := by omega
            rw [Nat.mod_eq_of_lt hlt] at hjvalmod
            exact hjvalmod
          rw [Fin.le_iff_val_le_val, hjval]
          exact Nat.succ_le_of_lt <| Nat.pos_of_ne_zero (by
            intro h0
            exact ht0 (Fin.ext h0))
        have htk : t ≤ k := by
          rw [Fin.le_iff_val_le_val, hk_last]
          exact Nat.le_pred_of_lt t.2
        exact hinside_const t hjt htk
      have hsum_rest :
          ∑ t ∈ Finset.univ.erase (0 : Fin h), d t =
            ∑ t ∈ Finset.univ.erase (0 : Fin h), d j := by
        refine Finset.sum_congr rfl fun t ht => ?_
        exact hinside_nonzero (Finset.mem_erase.mp ht).1
      have hqeq : (q : Int) = h * d j + (d 0 - d j) := by
        calc
          (q : Int) = ∑ t : Fin h, d t := hqsum
          _ = d 0 + ∑ t ∈ Finset.univ.erase (0 : Fin h), d t := by
                symm
                exact Finset.add_sum_erase Finset.univ (fun t : Fin h => d t) (Finset.mem_univ 0)
          _ = d 0 + ∑ t ∈ Finset.univ.erase (0 : Fin h), d j := by rw [hsum_rest]
          _ = d 0 + ((h - 1 : Nat) : Int) * d j := by simp
          _ = d 0 + (h - 1) * d j := by
                have h1 : 1 ≤ h := by omega
                rw [Nat.cast_sub h1]
                norm_num
          _ = h * d j + (d 0 - d j) := by ring
      refine ⟨0, d j, d 0 - d j, hdelta0, ?_, ?_, ?_⟩
      · simpa using hqeq
      · calc
          (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ (0 : Int)) : Int) = d 0 := by
            have hzero : @Fin.intCast h (by infer_instance) (0 : Int) = (0 : Fin h) := by
              exact fin_intCast_coe (h := h) (i := (0 : Fin h))
            rw [← hzero]
            exact hcast_rank (0 : Int)
          _ = d j + (d 0 - d j) := by omega
      · intro z hz
        have ht0 : @Fin.intCast h (by infer_instance) z ≠ 0 := by
          intro hEq
          have hz0 : z % h = 0 := by
            calc
              z % h = ((@Fin.intCast h (by infer_instance) z : Fin h) : Int) := by
                symm
                exact fin_intCast_coe_int (h := h) (z := z)
              _ = 0 := by simp [hEq]
          exact hz (by simpa using hz0)
        calc
          (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ z) : Int) =
              d (@Fin.intCast h (by infer_instance) z) := hcast_rank z
          _ = d j := hinside_nonzero ht0
    · exfalso
      have hj_lt_k : j < k := lt_of_le_of_ne hj_le_k hjk
      have hk_ge_two : 2 ≤ k.val := by
        have hjlt' : j.val < k.val := hj_lt_k
        omega
      have hge3 : 3 ≤ h := by
        omega
      have h2mod : ¬ ((2 : Int) % h = 0) := by
        intro hmod
        have hdvd : (h : Int) ∣ 2 := Int.dvd_iff_emod_eq_zero.mpr hmod
        have hle : (h : Int) ≤ 2 := Int.le_of_dvd (by norm_num) hdvd
        have hge3' : (3 : Int) ≤ h := by
          exact_mod_cast hge3
        omega
      let c2 : Int :=
        Module.finrank F (intertwiningSubmodule g.toLinearMap (ε ^ (2 : Int) • g.toLinearMap))
      have hE2 : c0 = c2 + 1 := by
        dsimp [c0, c2]
        exact_mod_cast hE 2 h2mod
      have hsum2_raw := proposition_2_4_h (hg := hg) (hh := hh) (hε := hε) (m := 2)
      have hsum2_left : (2 : Int) * c0 - (2 : Int) * c2 = 2 := by
        omega
      have hsum2' :
          (∑ i : Fin h,
            (((Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ (i : ℕ)) : Int) -
              (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ ((i : Int) + 2)) : Int)) ^ 2)) = 2 := by
        calc
          (∑ i : Fin h,
            (((Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ (i : ℕ)) : Int) -
              (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ ((i : Int) + 2)) : Int)) ^ 2))
              = (2 : Int) * c0 - (2 : Int) * c2 := by
                  simpa [c0, c2] using hsum2_raw.symm
          _ = 2 := hsum2_left
      have hsum2 : (∑ i : Fin h, a2 i) = 2 := by
        have hsum2a :
            ∑ i : Fin h, a2 i =
              ∑ i : Fin h,
                ((d i -
                  (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ ((i : Int) + 2)) : Int)) ^ 2) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          dsimp [a2, s2]
          rw [← hshift 2 i]
        have hsum2b :
            (∑ i : Fin h,
              ((d i -
                (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ ((i : Int) + 2)) : Int)) ^ 2)) =
              ∑ i : Fin h,
                (((Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ (i : ℕ)) : Int) -
                  (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ ((i : Int) + 2)) : Int)) ^ 2) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          change (((Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ ((i : Int))) : Int) -
              (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ ((i : Int) + 2)) : Int)) ^ 2) =
            (((Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ (i : ℕ)) : Int) -
              (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ ((i : Int) + 2)) : Int)) ^ 2)
          rw [zpow_natCast]
        calc
          ∑ i : Fin h, a2 i =
              ∑ i : Fin h,
                ((d i -
                  (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ ((i : Int) + 2)) : Int)) ^ 2) := hsum2a
          _ =
              ∑ i : Fin h,
                (((Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ (i : ℕ)) : Int) -
                  (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ ((i : Int) + 2)) : Int)) ^ 2) := hsum2b
          _ = 2 := hsum2'
      let km1 : Fin h := ⟨k.val - 1, by omega⟩
      have hkm1_lt_k : km1 < k := by
        rw [Fin.lt_def]
        dsimp [km1]
        omega
      have hj_le_km1 : j ≤ km1 := by
        rw [Fin.le_iff_val_le_val]
        dsimp [km1]
        have hjlt' : j.val < k.val := hj_lt_k
        omega
      have hd_km1 : d km1 = d j := by
        exact hinside_const km1 hj_le_km1 (le_of_lt hkm1_lt_k)
      have hs2_km1_eq0_or_gt : s2 km1 = 0 ∨ k < s2 km1 := by
        by_cases hk1 : k.val + 1 < h
        · right
          have hs2km1 : s2 km1 = (⟨k.val + 1, hk1⟩ : Fin h) := by
            have hidx : ((km1 : Int) + 2) = (k : Int) + 1 := by
              dsimp [km1]
              omega
            dsimp [s2]
            rw [hidx]
            simpa using
              (fin_intCast_coe (h := h) (i := (⟨k.val + 1, hk1⟩ : Fin h)))
          rw [hs2km1, Fin.lt_def]
          simp
        · left
          have hk_last : k.val = h - 1 := by
            omega
          apply Fin.ext
          change (((((km1 : Int) + 2) % h).toNat) = 0)
          have hk1eq : (km1 : Int) + 2 = h := by
            dsimp [km1]
            have hk_cast : (k : Int) = ((h - 1 : Nat) : Int) := by
              exact_mod_cast hk_last
            omega
          have hmod : (((km1 : Int) + 2) % h) = 0 := by
            rw [hk1eq]
            exact Int.emod_eq_zero_of_dvd (show (h : Int) ∣ h by exact dvd_rfl)
          simp [hmod]
      have hd_s2km1 : d (s2 km1) = d 0 := by
        cases hs2_km1_eq0_or_gt with
        | inl hs20 =>
            rw [hs20]
        | inr hklt =>
            exact houtside_eq0 (s2 km1) (Or.inr hklt)
      have ha2_km1_pos : 0 < a2 km1 := by
        have hne : d km1 - d (s2 km1) ≠ 0 := by
          rw [hd_km1, hd_s2km1]
          exact sub_ne_zero.mpr hd_j_ne
        simpa [a2] using sq_pos_iff.mpr hne
      by_cases hj1 : j = 1
      · have hk_not_last : k.val < h - 1 := by
          have hle : k.val ≤ h - 1 := Nat.le_pred_of_lt k.2
          have hneq : k.val ≠ h - 1 := by
            intro hk_last
            exact hcomp ⟨hj1, hk_last⟩
          exact lt_of_le_of_ne hle hneq
        have hjvalmod : j.val = 1 % h := by
          simpa using congrArg Fin.val hj1
        have hjval : j.val = 1 := by
          have hlt : 1 < h := by omega
          rw [Nat.mod_eq_of_lt hlt] at hjvalmod
          exact hjvalmod
        let u2 : Fin h := ⟨2, by omega⟩
        have hs2_zero : s2 0 = u2 := by
          dsimp [u2, s2]
          simpa using (fin_intCast_coe (h := h) (i := (⟨2, by omega⟩ : Fin h)))
        have hd_s2zero : d (s2 0) = d j := by
          rw [hs2_zero]
          exact hinside_const u2
            (by
              rw [Fin.le_iff_val_le_val, hjval]
              dsimp [u2]
              omega)
            (by
              rw [Fin.le_iff_val_le_val]
              dsimp [u2]
              omega)
        have ha2_zero_pos : 0 < a2 0 := by
          have hne : d 0 - d (s2 0) ≠ 0 := by
            rw [hd_s2zero]
            exact sub_ne_zero.mpr (Ne.symm hd_j_ne)
          simpa [a2] using sq_pos_iff.mpr hne
        have hs2_k_eq0_or_gt : s2 k = 0 ∨ k < s2 k := by
          by_cases hk2 : k.val + 2 < h
          · right
            have hs2k : s2 k = (⟨k.val + 2, hk2⟩ : Fin h) := by
              simpa [s2] using (fin_intCast_coe (h := h) (i := (⟨k.val + 2, hk2⟩ : Fin h)))
            rw [hs2k, Fin.lt_def]
            simp
          · left
            have hk_eq : k.val = h - 2 := by
              omega
            apply Fin.ext
            change (((((k : Int) + 2) % h).toNat) = 0)
            have hk_eq_int : (k : Int) + 2 = h := by
              have hk_cast : (k : Int) = ((h - 2 : Nat) : Int) := by
                exact_mod_cast hk_eq
              have h2le : 2 ≤ h := by omega
              rw [Nat.cast_sub h2le] at hk_cast
              omega
            have hmod : (((k : Int) + 2) % h) = 0 := by
              rw [hk_eq_int]
              exact Int.emod_eq_zero_of_dvd (show (h : Int) ∣ h by exact dvd_rfl)
            simp [hmod]
        have hd_s2k : d (s2 k) = d 0 := by
          cases hs2_k_eq0_or_gt with
          | inl hs20 =>
              rw [hs20]
          | inr hklt =>
              exact houtside_eq0 (s2 k) (Or.inr hklt)
        have ha2_k_pos : 0 < a2 k := by
          have hne : d k - d (s2 k) ≠ 0 := by
            rw [hd_k_eq, hd_s2k]
            exact sub_ne_zero.mpr hd_j_ne
          simpa [a2] using sq_pos_iff.mpr hne
        have hk_pos : 0 < k.val := by
          omega
        have hk_ne_zero : k ≠ 0 := by
          intro hk0
          have : k.val = 0 := by simpa using congrArg Fin.val hk0
          omega
        have hkm1_pos : 0 < km1.val := by
          dsimp [km1]
          omega
        have hkm1_ne_zero : km1 ≠ 0 := by
          intro h0
          have : km1.val = 0 := by simpa using congrArg Fin.val h0
          omega
        have hkm1_ne_k : km1 ≠ k := ne_of_lt hkm1_lt_k
        let R2 : Finset (Fin h) := (((Finset.univ.erase (0 : Fin h)).erase km1).erase k)
        have hsum2_decomp :
            ∑ i : Fin h, a2 i = a2 0 + a2 km1 + a2 k + ∑ i ∈ R2, a2 i := by
          rw [← Finset.add_sum_erase Finset.univ (fun i : Fin h => a2 i) (Finset.mem_univ 0)]
          have hkm1_mem : km1 ∈ Finset.univ.erase (0 : Fin h) := by
            exact Finset.mem_erase.mpr ⟨hkm1_ne_zero, Finset.mem_univ km1⟩
          rw [← Finset.add_sum_erase (Finset.univ.erase (0 : Fin h)) (fun i : Fin h => a2 i) hkm1_mem]
          have hk_mem'' : k ∈ (Finset.univ.erase (0 : Fin h)).erase km1 := by
            exact Finset.mem_erase.mpr
              ⟨fun hEq => hkm1_ne_k hEq.symm, Finset.mem_erase.mpr ⟨hk_ne_zero, Finset.mem_univ k⟩⟩
          rw [← Finset.add_sum_erase ((Finset.univ.erase (0 : Fin h)).erase km1) (fun i : Fin h => a2 i) hk_mem'']
          change a2 0 + (a2 km1 + (a2 k + ∑ i ∈ R2, a2 i)) = a2 0 + a2 km1 + a2 k + ∑ i ∈ R2, a2 i
          ring
        have hR2_nonneg : 0 ≤ ∑ i ∈ R2, a2 i := by
          exact Finset.sum_nonneg fun i hi => by
            dsimp [a2]
            exact sq_nonneg _
        have h1zero : 1 ≤ a2 0 := by
          omega
        have h1km1 : 1 ≤ a2 km1 := by
          omega
        have h1k : 1 ≤ a2 k := by
          omega
        rw [hsum2_decomp] at hsum2
        omega
      · have hjval_ne_one : j.val ≠ 1 := by
          intro hjval
          apply hj1
          apply Fin.ext
          have hlt : 1 < h := by omega
          simpa [Nat.mod_eq_of_lt hlt] using hjval
        have hj_ge_two : 2 ≤ j.val := by
          omega
        let jm2 : Fin h := ⟨j.val - 2, by omega⟩
        have hjm2_lt_j : jm2 < j := by
          rw [Fin.lt_def]
          dsimp [jm2]
          omega
        have hd_jm2 : d jm2 = d 0 := by
          exact houtside_eq0 jm2 (Or.inl hjm2_lt_j)
        have hs2_jm2 : s2 jm2 = j := by
          have hidx : ((jm2 : Int) + 2) = (j : Int) := by
            dsimp [jm2]
            omega
          dsimp [s2]
          rw [hidx]
          simp
        have ha2_jm2_pos : 0 < a2 jm2 := by
          have hne : d jm2 - d (s2 jm2) ≠ 0 := by
            rw [hd_jm2, hs2_jm2]
            exact sub_ne_zero.mpr (Ne.symm hd_j_ne)
          simpa [a2] using sq_pos_iff.mpr hne
        let u1 : Fin h := ⟨j.val + 1, by omega⟩
        have hs2_jm1 : s2 jm1 = u1 := by
          have hidx : ((jm1 : Int) + 2) = (j : Int) + 1 := by
            dsimp [jm1]
            omega
          dsimp [s2, u1]
          rw [hidx]
          simpa using (fin_intCast_coe (h := h) (i := (⟨j.val + 1, by omega⟩ : Fin h)))
        have hd_s2jm1 : d (s2 jm1) = d j := by
          rw [hs2_jm1]
          exact hinside_const u1
            (by
              rw [Fin.le_iff_val_le_val]
              dsimp [u1]
              omega)
            (by
              rw [Fin.le_iff_val_le_val]
              dsimp [u1]
              omega)
        have ha2_jm1_pos : 0 < a2 jm1 := by
          have hne : d jm1 - d (s2 jm1) ≠ 0 := by
            rw [hd_jm1, hd_s2jm1]
            exact sub_ne_zero.mpr (Ne.symm hd_j_ne)
          simpa [a2] using sq_pos_iff.mpr hne
        have hjm2_lt_jm1 : jm2 < jm1 := by
          rw [Fin.lt_def]
          dsimp [jm2, jm1]
          omega
        have hjm1_lt_km1 : jm1 < km1 := by
          rw [Fin.lt_def]
          dsimp [jm1, km1]
          have hjlt' : j.val < k.val := hj_lt_k
          omega
        have hjm2_ne_jm1 : jm2 ≠ jm1 := ne_of_lt hjm2_lt_jm1
        have hjm2_ne_km1 : jm2 ≠ km1 := ne_of_lt (lt_trans hjm2_lt_jm1 hjm1_lt_km1)
        have hjm1_ne_km1 : jm1 ≠ km1 := ne_of_lt hjm1_lt_km1
        let R2 : Finset (Fin h) := (((Finset.univ.erase jm2).erase jm1).erase km1)
        have hsum2_decomp :
            ∑ i : Fin h, a2 i = a2 jm2 + a2 jm1 + a2 km1 + ∑ i ∈ R2, a2 i := by
          rw [← Finset.add_sum_erase Finset.univ (fun i : Fin h => a2 i) (Finset.mem_univ jm2)]
          have hjm1_mem : jm1 ∈ Finset.univ.erase jm2 := by
            exact Finset.mem_erase.mpr ⟨hjm2_ne_jm1.symm, Finset.mem_univ jm1⟩
          rw [← Finset.add_sum_erase (Finset.univ.erase jm2) (fun i : Fin h => a2 i) hjm1_mem]
          have hkm1_mem : km1 ∈ (Finset.univ.erase jm2).erase jm1 := by
            exact Finset.mem_erase.mpr
              ⟨fun hEq => hjm1_ne_km1 hEq.symm, Finset.mem_erase.mpr ⟨hjm2_ne_km1.symm, Finset.mem_univ km1⟩⟩
          rw [← Finset.add_sum_erase ((Finset.univ.erase jm2).erase jm1) (fun i : Fin h => a2 i) hkm1_mem]
          change a2 jm2 + (a2 jm1 + (a2 km1 + ∑ i ∈ R2, a2 i)) =
            a2 jm2 + a2 jm1 + a2 km1 + ∑ i ∈ R2, a2 i
          ring
        have hR2_nonneg : 0 ≤ ∑ i ∈ R2, a2 i := by
          exact Finset.sum_nonneg fun i hi => by
            dsimp [a2]
            exact sq_nonneg _
        have h1jm2 : 1 ≤ a2 jm2 := by
          omega
        have h1jm1 : 1 ≤ a2 jm1 := by
          omega
        have h1km1 : 1 ≤ a2 km1 := by
          omega
        rw [hsum2_decomp] at hsum2
        omega

public theorem CFSG.proposition_2_4_k
    {F : Type*} [Field F]
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {q : ℕ} (hdim : Module.finrank F V = q) (hq : q ≥ 2)
    {g : V ≃ₗ[F] V} {h : ℕ} (hg : g ^ h = 1) (hh : h ≥ 2)
    {ε : F} (hε : IsPrimitiveRoot ε h)
    (hE : ∀ m : ℤ, ¬ (m % h = 0) →
      Module.finrank F (intertwiningSubmodule g.toLinearMap (ε ^ (0 : ℤ) • g.toLinearMap)) =
      Module.finrank F (intertwiningSubmodule g.toLinearMap (ε ^ m • g.toLinearMap)) + 1) :
    ∃ i : ℤ, ∃ n : ℤ, ∃ δ : ℤ, (δ = 1 ∨ δ = -1) ∧ q = h * n + δ ∧
    (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ i)) = n + δ ∧
    (∀ j : ℤ, ¬ ((j - i) % h) = 0 →
      (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ j)) = n) ∧
    ((n = 1 ∧ i = 0 ∧ δ = -1 ∧ h = q + 1) ∨
      0 < (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ (0 : ℤ)))) := by
  have hq2 : (2 : ℤ) ≤ q := by
    exact_mod_cast hq
  have hh2 : (2 : ℤ) ≤ h := by
    exact_mod_cast hh
  rcases proposition_2_4_j (hdim := hdim) (hg := hg) (hh := hh) (hε := hε) hE with
    ⟨i, n, δ, hδ, hqnδ, hni, hrest⟩
  by_cases hi0 : ((0 : ℤ) - i) % h = 0
  · have hspace : End.eigenspace g.toLinearMap (ε ^ i) =
        End.eigenspace g.toLinearMap (ε ^ (0 : ℤ)) := by
      apply eigenspace_eq_of_zpow_modEq (hge2 := hh) (g := g) (h := h) (ε := ε) (hε := hε)
      have hdivneg : (h : ℤ) ∣ -i := by
        exact Int.dvd_iff_emod_eq_zero.mpr (by simpa using hi0)
      have hdiv : (h : ℤ) ∣ i := by
        simpa [Int.dvd_neg] using hdivneg
      exact Int.modEq_zero_iff_dvd.mpr hdiv
    have h0eq : (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ (0 : ℤ)) : ℤ) = n + δ := by
      have hfin :
          (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ i) : ℤ) =
            (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ (0 : ℤ)) : ℤ) :=
        congrArg (fun W : Submodule F V => (Module.finrank F W : ℤ)) hspace
      calc
        (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ (0 : ℤ)) : ℤ) =
            (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ i) : ℤ) := by
              simpa using hfin.symm
        _ = n + δ := hni
    have hrest0 : ∀ j : ℤ, ¬ ((j - (0 : ℤ)) % h) = 0 →
        (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ j)) = n := by
      intro j hj
      have hji : ¬ ((j - i) % h) = 0 := by
        intro hji0
        have hji_div : (h : ℤ) ∣ j - i := by
          exact Int.dvd_iff_emod_eq_zero.mpr hji0
        have hji_mod : j - i ≡ 0 [ZMOD h] := Int.modEq_zero_iff_dvd.mpr hji_div
        have hi_div : (h : ℤ) ∣ -i := by
          exact Int.dvd_iff_emod_eq_zero.mpr (by simpa using hi0)
        have hi_mod : i ≡ 0 [ZMOD h] := by
          exact Int.modEq_zero_iff_dvd.mpr (by simpa [Int.dvd_neg] using hi_div)
        have hji_eq : j ≡ i [ZMOD h] := by
          have hji_div' : (h : ℤ) ∣ i - j := by
            simpa using (dvd_sub_comm.mp hji_div)
          exact Int.modEq_iff_dvd.mpr hji_div'
        have hj_mod : j ≡ 0 [ZMOD h] := hji_eq.trans hi_mod
        have hj_div : (h : ℤ) ∣ j := Int.modEq_zero_iff_dvd.mp hj_mod
        apply hj
        simpa [sub_zero] using Int.emod_eq_zero_of_dvd hj_div
      exact hrest j hji
    refine ⟨0, n, δ, hδ, hqnδ, h0eq, hrest0, ?_⟩
    by_cases hpos0 : 0 < (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ (0 : ℤ)))
    · exact Or.inr hpos0
    · have hzero0 : (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ (0 : ℤ))) = 0 := by
        exact Nat.eq_zero_of_not_pos hpos0
      have hzero0' : (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ (0 : ℤ)) : ℤ) = 0 := by
        exact_mod_cast hzero0
      have hnδ0 : n + δ = 0 := by
        omega
      have hn1 : n = 1 := by
        rcases hδ with hδ | hδ
        · exfalso
          nlinarith
        · nlinarith
      have hδm1 : δ = -1 := by
        rcases hδ with hδ | hδ
        · exfalso
          nlinarith
        · exact hδ
      have hhq1' : (h : ℤ) = q + 1 := by
        rw [hn1, hδm1] at hqnδ
        nlinarith
      have hhq1 : h = q + 1 := by
        exact_mod_cast hhq1'
      exact Or.inl ⟨hn1, rfl, hδm1, hhq1⟩
  · have h00eq : (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ (0 : ℤ)) : ℤ) = n := by
      exact hrest 0 hi0
    refine ⟨i, n, δ, hδ, hqnδ, hni, hrest, ?_⟩
    have hnpos : 0 < n := by
      rcases hδ with hδ | hδ <;> nlinarith [hqnδ, hq2, hh2]
    have hpos0' : (0 : ℤ) < (Module.finrank F <| End.eigenspace g.toLinearMap (ε ^ (0 : ℤ)) : ℤ) := by
      rw [h00eq]
      nlinarith
    exact Or.inr (by exact_mod_cast hpos0')
