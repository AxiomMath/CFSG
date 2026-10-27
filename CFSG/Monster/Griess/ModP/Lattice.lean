module

public import CFSG.Monster.Griess.Product
public import CFSG.Monster.SteinbergBQOddPrimeCongruenceTorsionFree
import Mathlib.NumberTheory.Padics.PadicVal.Basic

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Griess.ModP

open CFSG.Monster

variable (p : ℕ) [hp : Fact p.Prime]

theorem dyadic_le_ratLocal (hp2 : p ≠ 2) : dyadic ≤ ratLocal p := by
  rintro q ⟨k, hk⟩ h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1
    (hp.out.dvd_of_dvd_pow (h.trans hk)))

theorem natCast_mem_ratLocal (n : ℕ) : (n : ℚ) ∈ ratLocal p := natCast_mem _ n

theorem intCast_div_mem_ratLocal (a : ℤ) {b : ℤ} (hb : ¬ (p : ℤ) ∣ b) :
    (a : ℚ) / b ∈ ratLocal p := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hb (dvd_zero _)
  exact (mem_ratLocal_iff p).2 ⟨a, b, hb0, hb, rfl⟩

theorem inv_natCast_mem_ratLocal {n : ℕ} (hn : ¬ p ∣ n) : (n : ℚ)⁻¹ ∈ ratLocal p := by
  have h := intCast_div_mem_ratLocal p 1 (b := n) (by exact_mod_cast hn)
  rwa [Int.cast_one, one_div, Int.cast_natCast] at h

theorem eq_zero_of_forall_div_pow_mem {x : ℚ} (h : ∀ k : ℕ, x / (p : ℚ) ^ k ∈ ratLocal p) :
    x = 0 := by
  by_contra hx
  have hv : ∀ y : ℚ, y ∈ ratLocal p → 0 ≤ padicValRat p y := by
    intro y hy
    rw [padicValRat, padicValNat.eq_zero_of_not_dvd hy, Nat.cast_zero, sub_zero]
    exact Nat.cast_nonneg _
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have h1 := hv _ (h ((padicValRat p x).toNat + 1))
  rw [padicValRat.div hx (pow_ne_zero _ hp0), padicValRat.pow, padicValRat.self hp.out.one_lt]
    at h1
  have := Int.self_le_toNat (padicValRat p x)
  push_cast at h1
  omega

@[expose] def LatP (k : ℕ) : AddSubgroup SpaceB where
  carrier := {v | ∀ i, basisB.repr v i / (p : ℚ) ^ k ∈ ratLocal p}
  add_mem' {u v} hu hv i := by
    rw [map_add, Finsupp.add_apply, add_div]
    exact add_mem (hu i) (hv i)
  zero_mem' i := by
    rw [map_zero, Finsupp.zero_apply, zero_div]
    exact zero_mem _
  neg_mem' {v} hv i := by
    rw [map_neg, Finsupp.neg_apply, neg_div]
    exact neg_mem (hv i)

variable {p}

theorem mem_LatP {k : ℕ} {v : SpaceB} :
    v ∈ LatP p k ↔ ∀ i, basisB.repr v i / (p : ℚ) ^ k ∈ ratLocal p := Iff.rfl

theorem mem_LatP_iff_smul {k : ℕ} {v : SpaceB} :
    v ∈ LatP p k ↔ ((p : ℚ) ^ k)⁻¹ • v ∈ LatP p 0 := by
  simp only [mem_LatP, map_smul, Finsupp.smul_apply, smul_eq_mul, pow_zero, div_one]
  refine forall_congr' fun i => ?_
  rw [div_eq_inv_mul]

theorem smul_mem_LatP {r : ℚ} (hr : r ∈ ratLocal p) {k : ℕ} {v : SpaceB} (hv : v ∈ LatP p k) :
    r • v ∈ LatP p k := fun i => by
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, mul_div_assoc]
  exact mul_mem hr (hv i)

theorem LatP_anti {j k : ℕ} (hjk : j ≤ k) : LatP p k ≤ LatP p j := fun v hv i => by
  have e : basisB.repr v i / (p : ℚ) ^ j =
      (p : ℚ) ^ (k - j) * (basisB.repr v i / (p : ℚ) ^ k) := by
    have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    rw [← Nat.sub_add_cancel hjk, pow_add]
    field_simp
    rw [Nat.add_sub_cancel]
  rw [e]
  exact mul_mem (pow_mem (natCast_mem_ratLocal p p) _) (hv i)

theorem mem_LatP_zero_of_mem_BR (hp2 : p ≠ 2) {v : SpaceB} (hv : v ∈ BR) : v ∈ LatP p 0 := by
  have hD : ∀ i, basisB.repr v i ∈ dyadic := by
    induction hv using Submodule.span_induction with
    | mem x hx =>
      classical
      obtain ⟨k, rfl⟩ := hx
      intro i
      rw [basisB.repr_self, Finsupp.single_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    | zero =>
      intro i
      rw [map_zero, Finsupp.zero_apply]
      exact zero_mem _
    | add x y _ _ hx hy =>
      intro i
      rw [map_add, Finsupp.add_apply]
      exact add_mem (hx i) (hy i)
    | smul a x _ hx =>
      intro i
      change basisB.repr ((a : ℚ) • x) i ∈ dyadic
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact mul_mem a.2 (hx i)
  intro i
  rw [pow_zero, div_one]
  exact dyadic_le_ratLocal p hp2 (hD i)

theorem map_mem_LatP {f : SpaceB →ₗ[ℚ] SpaceB} (hf : ∀ i, f (basisB i) ∈ LatP p 0) {k : ℕ}
    {v : SpaceB} (hv : v ∈ LatP p k) : f v ∈ LatP p k := by
  rw [mem_LatP_iff_smul, ← map_smul]
  have hv0 := mem_LatP_iff_smul.1 hv
  rw [← basisB.sum_repr (((p : ℚ) ^ k)⁻¹ • v), map_sum]
  refine sum_mem fun i _ => ?_
  rw [map_smul]
  have hi := hv0 i
  rw [pow_zero, div_one] at hi
  exact smul_mem_LatP hi (hf i)

theorem map_mem_LatP_of_BR (hp2 : p ≠ 2) {f : SpaceB →ₗ[ℚ] SpaceB} (hf : ∀ x ∈ BR, f x ∈ BR)
    {k : ℕ} {v : SpaceB} (hv : v ∈ LatP p k) : f v ∈ LatP p k :=
  map_mem_LatP (fun i => mem_LatP_zero_of_mem_BR hp2 (hf _ (Submodule.subset_span ⟨i, rfl⟩))) hv

theorem gmul_mem_LatP_of_mem_zero (hp2 : p ≠ 2) {u : SpaceB} (hu : u ∈ LatP p 0) {k : ℕ}
    {v : SpaceB} (hv : v ∈ LatP p k) : gmul u v ∈ LatP p k := by
  refine map_mem_LatP (fun i => ?_) hv
  rw [← LinearMap.flip_apply gmul]
  refine map_mem_LatP (fun l => ?_) hu
  rw [LinearMap.flip_apply]
  exact mem_LatP_zero_of_mem_BR hp2
    (gmul_mem_BR (Submodule.subset_span ⟨l, rfl⟩) (Submodule.subset_span ⟨i, rfl⟩))

theorem gmul_mem_LatP (hp2 : p ≠ 2) {j k : ℕ} {u v : SpaceB} (hu : u ∈ LatP p j)
    (hv : v ∈ LatP p k) : gmul u v ∈ LatP p (j + k) := by
  rw [mem_LatP_iff_smul]
  have e : ((p : ℚ) ^ (j + k))⁻¹ • gmul u v =
      gmul (((p : ℚ) ^ j)⁻¹ • u) (((p : ℚ) ^ k)⁻¹ • v) := by
    rw [map_smul, map_smul, LinearMap.smul_apply, smul_smul, ← mul_inv, ← pow_add, add_comm k j]
  rw [e]
  exact gmul_mem_LatP_of_mem_zero hp2 (mem_LatP_iff_smul.1 hu) (mem_LatP_iff_smul.1 hv)

theorem eq_zero_of_forall_mem_LatP {v : SpaceB} (h : ∀ k, v ∈ LatP p k) : v = 0 := by
  refine basisB.repr.injective (Finsupp.ext fun i => ?_)
  rw [map_zero, Finsupp.zero_apply]
  exact eq_zero_of_forall_div_pow_mem p fun k => h k i

end CFSG.Monster.Griess.ModP
