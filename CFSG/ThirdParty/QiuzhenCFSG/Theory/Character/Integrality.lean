module

public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RepresentationTheory.Character
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.GroupTheory.Index

namespace CFSG
end CFSG
open CFSG

/-!
# Integrality of character values

Character values are algebraic integers: an eigenvalue of an endomorphism of
finite order is an algebraic integer, hence the trace is, hence `ρ.character g`
is for every representation `ρ`.
-/

noncomputable section

open scoped BigOperators

namespace CFSG.Theory.Character

universe u v

/-- An eigenvalue of an endomorphism of finite order is an algebraic integer. -/
public theorem eigen_value_isIntegral_of_pow_eq_one {V : Type v} [AddCommGroup V]
    [Module ℂ V] {f : V →ₗ[ℂ] V} {n : ℕ} (hn : 0 < n) (hf : f ^ n = 1)
    {z : ℂ} (hz : Module.End.HasEigenvalue f z) : IsIntegral ℤ z := by
  classical
  rcases Submodule.exists_mem_ne_zero_of_ne_bot hz with ⟨x, hxmem, hx0⟩
  have hx : f x = z • x := by
    have hker : x ∈ LinearMap.ker (f - z • 1) := by
      simpa [Module.End.eigenspace_def] using hxmem
    have hsub : (f - z • 1) x = 0 := (LinearMap.mem_ker).1 hker
    exact sub_eq_zero.mp (by simpa [LinearMap.sub_apply, LinearMap.smul_apply] using hsub)
  have hsmul : ∀ k : ℕ, (f ^ k) x = (z ^ k) • x := by
    intro k
    induction k with
    | zero => simp
    | succ k hk =>
        calc
          (f ^ (k + 1)) x = (f ^ k) (f x) := by rw [pow_succ]; rfl
          _ = (f ^ k) (z • x) := by rw [hx]
          _ = z • (f ^ k) x := by rw [map_smul]
          _ = z • ((z ^ k) • x) := by rw [hk]
          _ = (z ^ (k + 1)) • x := by
            rw [← mul_smul]
            congr 1
            rw [mul_comm, pow_succ]
  have hzpow : z ^ n = 1 := by
    have h : (z ^ n - 1) • x = 0 := by
      have h1 : (z ^ n) • x = x := by
        calc
          (z ^ n) • x = (f ^ n) x := by rw [hsmul n]
          _ = x := by rw [hf]; simp
      rw [sub_smul]
      rw [h1]
      simp
    have : z ^ n - 1 = 0 := by
      exact (smul_eq_zero.mp h).resolve_right hx0
    exact sub_eq_zero.mp this
  refine ⟨Polynomial.X ^ n - 1, ?_, ?_⟩
  · exact Polynomial.monic_X_pow_sub_C (1 : ℤ) hn.ne'
  · simp [hzpow]

/-- The trace of an endomorphism, all of whose eigenvalues are algebraic
integers, is an algebraic integer. -/
public theorem trace_isIntegral_of_forall_eigenvalue {V : Type v} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (f : V →ₗ[ℂ] V)
    (h : ∀ z : ℂ, Module.End.HasEigenvalue f z → IsIntegral ℤ z) :
    IsIntegral ℤ ((LinearMap.trace ℂ V) f) := by
  classical
  have hsplits : f.charpoly.Splits := IsAlgClosed.splits f.charpoly
  have htr : (LinearMap.trace ℂ V) f = f.charpoly.roots.sum :=
    Module.End.trace_eq_sum_roots_charpoly_of_splits hsplits
  have hmonic : f.charpoly.Monic := LinearMap.charpoly_monic f
  have hroot_integral : ∀ z : ℂ, z ∈ f.charpoly.roots → IsIntegral ℤ z := by
    intro z hz
    have hroot : f.charpoly.IsRoot z := (Polynomial.mem_roots hmonic.ne_zero).1 hz
    exact h z ((Module.End.hasEigenvalue_iff_isRoot_charpoly f z).2 hroot)
  have hsum_int : IsIntegral ℤ f.charpoly.roots.sum := by
    exact (Multiset.induction_on f.charpoly.roots
      (p := fun s : Multiset ℂ => s ≤ f.charpoly.roots → IsIntegral ℤ s.sum)
      (fun _ => ⟨Polynomial.X, Polynomial.monic_X, by simp⟩)
      (fun z s hs hle => by
        simpa using
          (hroot_integral z (Multiset.mem_of_le hle (Multiset.mem_cons_self z s))).add
            (hs (le_trans (Multiset.le_cons_self s z) hle))))
      le_rfl
  rw [htr]
  exact hsum_int

/-- If `f` commutes with an idempotent `g`, then every eigenvalue of `f * g`
is either zero or an eigenvalue of `f`. -/
public theorem hasEigenvalue_of_mul_hasEigenvalue {V : Type v} [AddCommGroup V]
    [Module ℂ V] {f g : V →ₗ[ℂ] V} (hcomm : f * g = g * f) (hidem : g * g = g)
    {z : ℂ} (hz : Module.End.HasEigenvalue (f * g) z) :
    z = 0 ∨ Module.End.HasEigenvalue f z := by
  classical
  rcases Submodule.exists_mem_ne_zero_of_ne_bot hz with ⟨x, hxmem, hx0⟩
  have hx : (f * g) x = z • x := by
    have hker : x ∈ LinearMap.ker (f * g - z • 1) := by
      simpa [Module.End.eigenspace_def] using hxmem
    have hsub : (f * g - z • 1) x = 0 := (LinearMap.mem_ker).1 hker
    exact sub_eq_zero.mp (by simpa [LinearMap.sub_apply, LinearMap.smul_apply] using hsub)
  by_cases hg : g x = 0
  · left
    have hz0 : z • x = 0 := by
      calc
        z • x = (f * g) x := hx.symm
        _ = f (g x) := rfl
        _ = 0 := by rw [hg, map_zero]
    exact (smul_eq_zero.mp hz0).resolve_right hx0
  · right
    have hmem : g x ∈ Module.End.eigenspace f z := by
      rw [Module.End.eigenspace_def]
      rw [LinearMap.mem_ker]
      have hfgx : f (g x) = z • (g x) := by
        have hgelim : g * (f * g) = (f * g) * g := by
          ext y
          calc
            g ((f * g) y) = (g * (f * g)) y := rfl
            _ = ((f * g) * g) y := by rw [← mul_assoc, hcomm]
            _ = (f * g) (g y) := rfl
        have hggx : g (g x) = g x := by
          change (g * g) x = g x
          rw [hidem]
        have hgfg : (f * g) (g x) = g ((f * g) x) := by
          change ((f * g) * g) x = (g * (f * g)) x
          rw [← hgelim]
        calc
          f (g x) = (f * g) (g x) := by
            change f (g x) = f (g (g x))
            rw [hggx]
          _ = g ((f * g) x) := hgfg
          _ = g (z • x) := by rw [hx]
          _ = z • (g x) := by rw [map_smul]
      simp [LinearMap.sub_apply, LinearMap.smul_apply, hfgx]
    rw [Module.End.hasEigenvalue_iff]
    intro hbot
    have hgx0 : g x = 0 := by
      exact (Submodule.mem_bot ℂ).1 (hbot ▸ hmem)
    exact hg hgx0

/-- Character values are algebraic integers. -/
public theorem character_value_isIntegral {G : Type u} [Group G] [Fintype G]
    {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    IsIntegral ℤ (ρ.character g) := by
  change IsIntegral ℤ ((LinearMap.trace ℂ V) (ρ g))
  refine trace_isIntegral_of_forall_eigenvalue (ρ g) ?_
  intro z hz
  have hf : (ρ g) ^ orderOf g = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  exact eigen_value_isIntegral_of_pow_eq_one (orderOf_pos g) hf hz

end CFSG.Theory.Character
