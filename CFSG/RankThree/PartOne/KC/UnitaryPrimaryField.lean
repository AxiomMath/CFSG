module

public import CFSG.RankThree.PartOne.KC.UnitaryPrimaryDual
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteAutomorphism
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.PartOne.KCUnitary

open Polynomial CFSG.LocalAnalysis.ComponentInitial

section Theta

variable {K : Type*} [Field K] {σ : K →+* K} {a : K[X]} [Fact (Irreducible a)]

theorem root_ne_zero (h0 : a.coeff 0 ≠ 0) : (AdjoinRoot.root a) ≠ 0 := by
  intro h
  apply h0
  have h1 : aeval (AdjoinRoot.root a) a = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  rw [h, aeval_def, eval₂_at_zero] at h1
  exact (algebraMap K (AdjoinRoot a)).injective (by rw [h1, map_zero])

theorem eval₂_theta_root_inv (h0 : a.coeff 0 ≠ 0) (hself : dualPoly σ a = a) :
    a.eval₂ ((algebraMap K (AdjoinRoot a)).comp σ) (AdjoinRoot.root a)⁻¹ = 0 := by
  have hρ := root_ne_zero (a := a) h0
  have h1 : aeval (AdjoinRoot.root a) (dualPoly σ a) = 0 := by
    rw [hself, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hc : (σ (a.coeff 0))⁻¹ ≠ 0 := inv_ne_zero ((map_ne_zero σ).mpr h0)
  rw [dualPoly, map_mul, aeval_C, mul_eq_zero] at h1
  have h2 : aeval (AdjoinRoot.root a) (a.map σ).reverse = 0 := by
    refine h1.resolve_left ?_
    exact (map_ne_zero (algebraMap K (AdjoinRoot a))).mpr hc
  have h3 := aeval_reflect_of_unit (Units.mk0 (AdjoinRoot.root a) hρ) (a.map σ)
    (N := (a.map σ).natDegree) le_rfl
  simp only [Units.val_mk0, Units.val_inv_eq_inv_val] at h3
  rw [reverse] at h2
  have h4 : (AdjoinRoot.root a) ^ (a.map σ).natDegree *
      aeval (AdjoinRoot.root a)⁻¹ (a.map σ) = 0 := by rw [← h3]; exact h2
  have h5 : aeval (AdjoinRoot.root a)⁻¹ (a.map σ) = 0 :=
    (mul_eq_zero.mp h4).resolve_left (pow_ne_zero _ hρ)
  rwa [aeval_def, eval₂_map] at h5


variable (σ a)

@[expose] noncomputable def theta (h0 : a.coeff 0 ≠ 0) (hself : dualPoly σ a = a) :
    AdjoinRoot a →+* AdjoinRoot a :=
  AdjoinRoot.lift ((algebraMap K (AdjoinRoot a)).comp σ) (AdjoinRoot.root a)⁻¹
    (eval₂_theta_root_inv h0 hself)

variable {σ a} (h0 : a.coeff 0 ≠ 0) (hself : dualPoly σ a = a)

theorem theta_algebraMap (c : K) :
    theta σ a h0 hself (algebraMap K (AdjoinRoot a) c) = algebraMap K (AdjoinRoot a) (σ c) := by
  rw [AdjoinRoot.algebraMap_eq, theta, AdjoinRoot.lift_of]
  rfl

theorem theta_root : theta σ a h0 hself (AdjoinRoot.root a) = (AdjoinRoot.root a)⁻¹ := by
  rw [theta, AdjoinRoot.lift_root]

theorem theta_theta (hσ : Function.Involutive σ) (e : AdjoinRoot a) :
    theta σ a h0 hself (theta σ a h0 hself e) = e := by
  have hρ := root_ne_zero (a := a) h0
  have : (theta σ a h0 hself).comp (theta σ a h0 hself) = RingHom.id (AdjoinRoot a) := by
    apply AdjoinRoot.ringHom_ext
    · ext c
      change theta σ a h0 hself (theta σ a h0 hself (algebraMap K (AdjoinRoot a) c)) = _
      rw [theta_algebraMap, theta_algebraMap, hσ]
      rfl
    · change theta σ a h0 hself (theta σ a h0 hself (AdjoinRoot.root a)) = _
      rw [theta_root, map_inv₀, theta_root, inv_inv]
      rfl
  exact congrArg (fun f : AdjoinRoot a →+* AdjoinRoot a => f e) this


instance : Module.Finite K (AdjoinRoot a) :=
  (AdjoinRoot.powerBasis (Fact.out : Irreducible a).ne_zero).finite

theorem trace_theta [Finite K] (z : AdjoinRoot a) :
    Algebra.trace K (AdjoinRoot a) (theta σ a h0 hself z) =
      σ (Algebra.trace K (AdjoinRoot a) z) := by
  have : Finite (AdjoinRoot a) := Module.finite_of_finite K
  apply (algebraMap K (AdjoinRoot a)).injective
  rw [FiniteField.algebraMap_trace_eq_sum_pow K (AdjoinRoot a) (theta σ a h0 hself z),
    ← theta_algebraMap h0 hself, FiniteField.algebraMap_trace_eq_sum_pow K (AdjoinRoot a) z,
    map_sum]
  simp [map_pow]

end Theta

section FiniteField

variable {K : Type*} [Field K] {a : K[X]} [Fact (Irreducible a)]

theorem finrank_adjoinRoot : Module.finrank K (AdjoinRoot a) = a.natDegree := by
  rw [(AdjoinRoot.powerBasis (Fact.out : Irreducible a).ne_zero).finrank,
    AdjoinRoot.powerBasis_dim]

variable {ℓ f : ℕ} (hK : UnitaryFieldData ℓ f K)
include hK

theorem natCard_adjoinRoot : Nat.card (AdjoinRoot a) = ℓ ^ (2 * (f * a.natDegree)) := by
  have := hK.finite
  rw [Module.natCard_eq_pow_finrank (K := K) (V := AdjoinRoot a), hK.card, finrank_adjoinRoot,
    ← pow_mul]
  congr 1
  ring

theorem unitaryFieldData_adjoinRoot : UnitaryFieldData ℓ (f * a.natDegree) (AdjoinRoot a) where
  prime := hK.prime
  one_le := Nat.mul_pos hK.one_le (Irreducible.natDegree_pos Fact.out)
  card := natCard_adjoinRoot hK


variable (h0 : a.coeff 0 ≠ 0) (hself : dualPoly hK.bar a = a)
include h0 hself

theorem theta_eq_bar (e : AdjoinRoot a) :
    theta hK.bar a h0 hself e = (unitaryFieldData_adjoinRoot hK (a := a)).bar e := by
  classical
  have hd : 0 < a.natDegree := Irreducible.natDegree_pos Fact.out
  have hfd : 0 < f * a.natDegree := Nat.mul_pos hK.one_le hd
  have hσ : Function.Involutive hK.bar := hK.bar_bar
  obtain ⟨φ, hφ, hord, hzp, hcard, -⟩ := finite_field_automorphism_fixed_field_cardinality
    hK.prime (by omega : 1 ≤ 2 * (f * a.natDegree)) (natCard_adjoinRoot hK)
  let θe : AdjoinRoot a ≃+* AdjoinRoot a :=
    { toFun := theta hK.bar a h0 hself
      invFun := theta hK.bar a h0 hself
      left_inv := theta_theta h0 hself hσ
      right_inv := theta_theta h0 hself hσ
      map_mul' := map_mul _
      map_add' := map_add _ }
  have hθe : ∀ e, θe e = theta hK.bar a h0 hself e := fun e => rfl
  have hθ2 : θe ^ 2 = 1 := by
    ext e
    change θe (θe e) = e
    rw [hθe, hθe, theta_theta h0 hself hσ]
  have hθ1 : θe ≠ 1 := by
    intro h
    obtain ⟨c, hc⟩ := hK.exists_bar_ne
    apply hc
    apply (algebraMap K (AdjoinRoot a)).injective
    rw [← theta_algebraMap h0 hself, ← hθe]
    exact congrArg (fun r : AdjoinRoot a ≃+* AdjoinRoot a => r (algebraMap K (AdjoinRoot a) c)) h
  have hcyc : IsCyclic (AdjoinRoot a ≃+* AdjoinRoot a) :=
    isCyclic_iff_exists_zpowers_eq_top.mpr ⟨φ, hzp⟩
  have hfin : Finite (AdjoinRoot a ≃+* AdjoinRoot a) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have hfintype : Fintype (AdjoinRoot a ≃+* AdjoinRoot a) := Fintype.ofFinite _
  set ψ : AdjoinRoot a ≃+* AdjoinRoot a := φ ^ (f * a.natDegree) with hψ
  have hψ2 : ψ ^ 2 = 1 := by
    rw [hψ, ← pow_mul, mul_comm, ← hord]
    exact pow_orderOf_eq_one φ
  have hψ1 : ψ ≠ 1 :=
    pow_ne_one_of_lt_orderOf hfd.ne' (by rw [hord]; omega)
  have hψθ : θe = ψ := by
    by_contra hne
    have hsub : ({1, θe, ψ} : Finset (AdjoinRoot a ≃+* AdjoinRoot a)) ⊆
        Finset.univ.filter fun g => g ^ 2 = 1 := by
      intro g hg
      simp only [Finset.mem_insert, Finset.mem_singleton] at hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hg with rfl | rfl | rfl
      · exact one_pow 2
      · exact hθ2
      · exact hψ2
    have h3 : ({1, θe, ψ} : Finset (AdjoinRoot a ≃+* AdjoinRoot a)).card = 3 :=
      Finset.card_eq_three.mpr ⟨1, θe, ψ, hθ1.symm, hψ1.symm, hne, rfl⟩
    have := (Finset.card_le_card hsub).trans (IsCyclic.card_pow_eq_one_le (by norm_num : 0 < 2))
    omega
  have hpow : ∀ (k : ℕ) (z : AdjoinRoot a), (φ ^ k) z = z ^ ℓ ^ k := by
    intro k
    induction k with
    | zero => intro z; simp
    | succ k ih =>
      intro z
      rw [pow_succ', pow_succ]
      change φ ((φ ^ k) z) = _
      rw [ih, hφ, ← pow_mul, ← pow_succ]
  have := hpow (f * a.natDegree) e
  rw [← hθe, hψθ, hψ, this]
  rfl

theorem odd_natDegree_of_selfDual : Odd a.natDegree := by
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨e, he⟩ := hodd
  obtain ⟨c, hc⟩ := hK.exists_bar_ne
  apply hc
  have h1 := theta_algebraMap h0 hself c
  rw [theta_eq_bar hK h0 hself, UnitaryFieldData.bar_apply] at h1
  apply (algebraMap K (AdjoinRoot a)).injective
  rw [← h1, ← map_pow]
  congr 1
  have := hK.finite
  have : Fintype K := Fintype.ofFinite K
  have hcard := FiniteField.pow_card_pow e c
  rw [← Nat.card_eq_fintype_card, hK.card, ← pow_mul] at hcard
  rw [he]
  convert hcard using 2
  ring_nf

end FiniteField

end CFSG.RankThree.PartOne.KCUnitary
