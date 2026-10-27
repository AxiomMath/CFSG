module

public import CFSG.Quasithin.Background.G11Bridge

public section

namespace CFSG.Quasithin.C58.G64D

open CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

abbrev dl (g : GLV V) : V →ₗ[ZMod 2] V := (g : V →ₗ[ZMod 2] V) - LinearMap.id

section Lemmas

variable [Finite V]

theorem commSpace_zpowers_eq_range (g : GLV V) :
    commSpace (Subgroup.zpowers g) ⊤ = LinearMap.range (dl g) :=
  commSpace_zpowers_top g

theorem datum_add_self (v : V) : v + v = 0 := by
  have h : (2 : ZMod 2) = 0 := rfl
  rw [← two_smul (ZMod 2) v, h, zero_smul]

theorem datum_neg_eq (v : V) : -v = v :=
  (eq_neg_of_add_eq_zero_right (datum_add_self v)).symm

theorem datum_sub_eq_add (a b : V) : a - b = a + b := by
  rw [sub_eq_add_neg, datum_neg_eq]

theorem datum_dl_apply (g : GLV V) (v : V) : dl g v = g v - v := rfl

theorem datum_inv_mul_apply (x : GLV V) (v : V) : x⁻¹ (x v) = v :=
  congrArg (fun g : GLV V => g v) (inv_mul_cancel x)

theorem datum_mul_inv_apply (x : GLV V) (v : V) : x (x⁻¹ v) = v :=
  congrArg (fun g : GLV V => g v) (mul_inv_cancel x)

theorem datum_pow_three_apply {x : GLV V} (hx : x ^ 3 = 1) (v : V) : x (x (x v)) = v := by
  have h : x * (x * x) = 1 := by rw [← pow_three]; exact hx
  exact congrArg (fun g : GLV V => g v) h

theorem datum_sum_dl {x : GLV V} (hx : x ^ 3 = 1) (u : V) :
    dl x u + x (dl x u) + x (x (dl x u)) = 0 := by
  have h3 := datum_pow_three_apply hx
  simp only [datum_dl_apply, map_sub, h3]
  abel

theorem isCompl_range_ker_dl {x : GLV V} (hx : x ^ 3 = 1) :
    IsCompl (LinearMap.range (dl x)) (LinearMap.ker (dl x)) := by
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro w hw hk
    obtain ⟨u, hu⟩ := LinearMap.mem_range.1 hw
    have hfix : x w = w := by
      have h0 : dl x w = 0 := LinearMap.mem_ker.1 hk
      rw [datum_dl_apply, sub_eq_zero] at h0
      exact h0
    have hs := datum_sum_dl hx u
    rw [hu, hfix, hfix, datum_add_self, zero_add] at hs
    exact hs
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have h1 : dl x (x v) ∈ LinearMap.range (dl x) := LinearMap.mem_range_self _ _
    have h2 : v + x v + x (x v) ∈ LinearMap.ker (dl x) := by
      rw [LinearMap.mem_ker, datum_dl_apply, map_add, map_add, datum_pow_three_apply hx v]
      abel
    have h3 : dl x (x v) + (v + x v + x (x v)) = v := by
      rw [datum_dl_apply x (x v),
        show x (x v) - x v + (v + x v + x (x v)) = v + (x (x v) + x (x v)) by abel,
        datum_add_self, add_zero]
    have h4 := Submodule.add_mem_sup h1 h2
    rwa [h3] at h4

theorem datum_range_dl_conj (g h : GLV V) :
    LinearMap.range (dl (g * h * g⁻¹)) = conjSub g (LinearMap.range (dl h)) := by
  ext v
  rw [mem_conjSub]
  constructor
  · intro hv
    obtain ⟨u, hu⟩ := LinearMap.mem_range.1 hv
    refine LinearMap.mem_range.2 ⟨g⁻¹ u, ?_⟩
    have key : g⁻¹ v = h (g⁻¹ u) - g⁻¹ u := by
      rw [← hu, datum_dl_apply, map_sub]
      congr 1
      exact datum_inv_mul_apply g (h (g⁻¹ u))
    rw [datum_dl_apply]
    exact key.symm
  · intro hy
    obtain ⟨y, hy⟩ := LinearMap.mem_range.1 hy
    have hy' : h y - y = g⁻¹ v := hy
    refine LinearMap.mem_range.2 ⟨g y, ?_⟩
    rw [datum_dl_apply]
    show g (h (g⁻¹ (g y))) - g y = v
    rw [datum_inv_mul_apply, ← map_sub g (h y) y, hy', datum_mul_inv_apply]

end Lemmas

end CFSG.Quasithin.C58.G64D
