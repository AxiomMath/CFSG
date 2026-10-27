module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.Quasithin.H13.L827X

open Finset

private theorem add_self_eq_zero_of_zmod2 {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (x : W) : x + x = 0 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [← two_smul (ZMod 2) x, h2, zero_smul]

private theorem sub_eq_of_add_self_eq_zero {W : Type*} [AddCommGroup W]
    (h2 : ∀ x : W, x + x = 0) (a b d : W) (h : a + b + d = 0) : d - b = a := by
  have hneg : ∀ x : W, -x = x := fun x => neg_eq_iff_add_eq_zero.mpr (h2 x)
  have h4 : b + d = -a := eq_neg_of_add_eq_zero_right (by rw [← add_assoc]; exact h)
  rw [sub_eq_add_neg, hneg b, add_comm, h4, hneg a]

private theorem conj_pow_of_mul_self_eq_one {A : Type*} [Monoid A] (t y : A) (ht : t * t = 1)
    (k : ℕ) : t * y ^ k * t = (t * y * t) ^ k := by
  induction k with
  | zero => simp [ht]
  | succ k ih =>
    rw [pow_succ (t * y * t) k, ← ih, pow_succ y k]
    calc t * (y ^ k * y) * t = t * y ^ k * (t * t) * (y * t) := by
          rw [ht]; simp only [mul_one, mul_assoc]
      _ = t * y ^ k * t * (t * y * t) := by simp only [mul_assoc]

private theorem pow_two_mul_eq_pow_sub {A : Type*} [Monoid A] (y : A) (m k : ℕ)
    (hy : y ^ (2 * m + 1) = 1) (hk : k ≤ 2 * m + 1) :
    (y ^ (2 * m)) ^ k = y ^ (2 * m + 1 - k) := by
  have h1 : (y ^ (2 * m)) ^ k * y ^ k = 1 := by
    rw [← pow_mul, ← pow_add, show 2 * m * k + k = (2 * m + 1) * k by ring, pow_mul, hy, one_pow]
  have h2 : y ^ k * y ^ (2 * m + 1 - k) = 1 := by
    rw [← pow_add, add_tsub_cancel_of_le hk, hy]
  calc (y ^ (2 * m)) ^ k = (y ^ (2 * m)) ^ k * (y ^ k * y ^ (2 * m + 1 - k)) := by
        rw [h2, mul_one]
    _ = ((y ^ (2 * m)) ^ k * y ^ k) * y ^ (2 * m + 1 - k) := by rw [mul_assoc]
    _ = y ^ (2 * m + 1 - k) := by rw [h1, one_mul]

private theorem geom_sum_split {A : Type*} [Ring A] (y : A) (m : ℕ) :
    ∑ j ∈ range (2 * m + 1), y ^ j =
      1 + (∑ i ∈ range m, y ^ (i + 1)) + ∑ i ∈ range m, y ^ (2 * m + 1 - (i + 1)) := by
  have hA : ∑ j ∈ range (2 * m + 1), y ^ j = ∑ j ∈ range (2 * m), y ^ (j + 1) + 1 := by
    rw [Finset.sum_range_succ', pow_zero]
  have hB : ∑ j ∈ range (2 * m), y ^ (j + 1) =
      ∑ i ∈ range m, y ^ (i + 1) + ∑ i ∈ range m, y ^ (m + i + 1) := by
    rw [two_mul, Finset.sum_range_add]
  have hC : ∑ i ∈ range m, y ^ (2 * m + 1 - (i + 1)) = ∑ i ∈ range m, y ^ (m + i + 1) := by
    have hrefl : ∑ j ∈ range m, y ^ (m + (m - 1 - j) + 1) = ∑ j ∈ range m, y ^ (m + j + 1) :=
      Finset.sum_range_reflect (fun i => y ^ (m + i + 1)) m
    rw [← hrefl]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi' := Finset.mem_range.mp hi
    rw [show 2 * m + 1 - (i + 1) = m + (m - 1 - i) + 1 by omega]
  rw [hA, hB, hC]
  abel

private theorem commute_sum_pow_sub_one {A : Type*} [Ring A] (y : A) (m : ℕ) :
    Commute (∑ i ∈ range m, y ^ (i + 1)) (y - 1) :=
  Commute.sum_left _ _ _ (fun i _ => ((Commute.refl y).pow_left (i + 1)).sub_right
    (Commute.one_right _))

private theorem finrank_le_two_mul_finrank_range {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (g : V →ₗ[K] V) (P : Submodule K V)
    (hP : ∀ w ∈ P, g w = 0 → ∃ v ∈ P, g v = w) :
    Module.finrank K P ≤ 2 * Module.finrank K (LinearMap.range g) := by
  have hrk := LinearMap.finrank_range_add_finrank_ker (g.comp P.subtype)
  have hle : Module.finrank K (LinearMap.range (g.comp P.subtype)) ≤
      Module.finrank K (LinearMap.range g) :=
    Submodule.finrank_mono (LinearMap.range_comp_le_range _ _)
  have hmem : ∀ x : LinearMap.ker (g.comp P.subtype),
      (P.subtype.comp (LinearMap.ker (g.comp P.subtype)).subtype) x ∈
        LinearMap.range (g.comp P.subtype) := by
    rintro ⟨⟨z, hz⟩, hk⟩
    have hgz : g z = 0 := by simpa using hk
    obtain ⟨v, hv, hgv⟩ := hP z hz hgz
    exact LinearMap.mem_range.mpr ⟨⟨v, hv⟩, hgv⟩
  let ψ : LinearMap.ker (g.comp P.subtype) →ₗ[K] LinearMap.range (g.comp P.subtype) :=
    LinearMap.codRestrict (LinearMap.range (g.comp P.subtype))
      (P.subtype.comp (LinearMap.ker (g.comp P.subtype)).subtype) hmem
  have hinj : Function.Injective ψ := by
    intro x y hxy
    have h1 := congrArg (fun z : LinearMap.range (g.comp P.subtype) => (z : V)) hxy
    have h2 : x.1.1 = y.1.1 := h1
    exact Subtype.ext (Subtype.ext h2)
  have hker := LinearMap.finrank_le_finrank_of_injective hinj
  omega

theorem dihedral_rank_count {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] {n : ℕ} (hn : Odd n) (y t : Module.End (ZMod 2) W)
    (hy : y ^ n = 1) (ht : t * t = 1) (hty : t * y * t = y ^ (n - 1)) :
    Module.finrank (ZMod 2) (LinearMap.range (y - 1)) ≤
      2 * Module.finrank (ZMod 2) (LinearMap.range (t - 1)) := by
  obtain ⟨m, rfl⟩ := hn
  have hm1 : 2 * m + 1 - 1 = 2 * m := by omega
  rw [hm1] at hty
  have hterm : ∀ i ∈ range m, t * y ^ (i + 1) * t = y ^ (2 * m + 1 - (i + 1)) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [conj_pow_of_mul_self_eq_one t y ht, hty,
      pow_two_mul_eq_pow_sub y m (i + 1) hy (by omega)]
  have htct : t * (∑ i ∈ range m, y ^ (i + 1)) * t =
      ∑ i ∈ range m, y ^ (2 * m + 1 - (i + 1)) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl hterm
  have he : (∑ j ∈ range (2 * m + 1), y ^ j) * (y - 1) = 0 := by
    rw [geom_sum_mul, hy, sub_self]
  have hcomm := (commute_sum_pow_sub_one y m).eq
  have h2 : ∀ x : W, x + x = 0 := add_self_eq_zero_of_zmod2
  have hsub : ∀ x : W, (t - 1) x = t x - x := fun x => rfl
  refine finrank_le_two_mul_finrank_range (t - 1) (LinearMap.range (y - 1)) ?_
  rintro w ⟨u, rfl⟩ hkw
  have htw : t ((y - 1) u) = (y - 1) u := sub_eq_zero.mp ((hsub _).symm.trans hkw)
  have hcw : (∑ i ∈ range m, y ^ (i + 1)) ((y - 1) u) =
      (y - 1) ((∑ i ∈ range m, y ^ (i + 1)) u) :=
    congrArg (fun F : Module.End (ZMod 2) W => F u) hcomm
  have hS : (y - 1) u + (∑ i ∈ range m, y ^ (i + 1)) ((y - 1) u) +
      (∑ i ∈ range m, y ^ (2 * m + 1 - (i + 1))) ((y - 1) u) = 0 := by
    have h0 : (∑ j ∈ range (2 * m + 1), y ^ j) ((y - 1) u) = 0 :=
      congrArg (fun F : Module.End (ZMod 2) W => F u) he
    rw [geom_sum_split y m] at h0
    exact h0
  have htc : t ((∑ i ∈ range m, y ^ (i + 1)) ((y - 1) u)) =
      (∑ i ∈ range m, y ^ (2 * m + 1 - (i + 1))) ((y - 1) u) := by
    have h : t ((∑ i ∈ range m, y ^ (i + 1)) (t ((y - 1) u))) =
        (∑ i ∈ range m, y ^ (2 * m + 1 - (i + 1))) ((y - 1) u) :=
      congrArg (fun F : Module.End (ZMod 2) W => F ((y - 1) u)) htct
    rw [htw] at h
    exact h
  refine ⟨(∑ i ∈ range m, y ^ (i + 1)) ((y - 1) u),
    LinearMap.mem_range.mpr ⟨(∑ i ∈ range m, y ^ (i + 1)) u, hcw.symm⟩, ?_⟩
  rw [hsub, htc]
  exact sub_eq_of_add_self_eq_zero h2 _ _ _ hS

end CFSG.Quasithin.H13.L827X
