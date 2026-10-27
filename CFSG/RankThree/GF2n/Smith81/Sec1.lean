module

public import CFSG.GroupTheory.HuppertProduct.Mho
public import CFSG.RankThree.GF2n.Stroth80.Defs

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

theorem exists_dihedral_eight [Finite G] {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (h4 : 4 ∣ orderOf (x * y)) :
    ∃ w : G, w * w = 1 ∧ orderOf (x * w) = 4 ∧
      (x * w) ^ 2 = (x * y) ^ (orderOf (x * y) / 2) ∧
      ∃ d ∈ Subgroup.closure ({x, y} : Set G), w = d * x * d⁻¹ ∨ w = d * y * d⁻¹ := by
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  set r := x * y with hr
  have hrinv : r⁻¹ = y * x := by rw [hr, mul_inv_rev, hxinv, hyinv]
  have hxrx : x * r * x⁻¹ = r⁻¹ := by
    rw [hrinv, hr, hxinv]
    calc x * (x * y) * x = (x * x) * y * x := by group
      _ = y * x := by rw [hx, one_mul]
  have hconj : ∀ k : ℤ, x * r ^ k * x = r ^ (-k) := by
    intro k
    have := conj_zpow (a := x) (b := r) (i := k)
    rw [hxrx, inv_zpow', hxinv] at this
    exact this.symm
  have hyx : y = x * r := by rw [hr, ← mul_assoc, hx, one_mul]
  have hord : 0 < orderOf r := orderOf_pos r
  obtain ⟨m', hm'⟩ := h4
  have hm'pos : 0 < m' := by omega
  have hrpow : r ^ (4 * m') = 1 := by rw [← hm']; exact pow_orderOf_eq_one r
  have hD : ∀ k : ℕ, r ^ k ∈ Subgroup.closure ({x, y} : Set G) := fun k =>
    Subgroup.pow_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))) k
  refine ⟨r ^ m' * x, ?_, ?_, ?_, ?_⟩
  · have h1 := hconj (m' : ℤ)
    calc r ^ m' * x * (r ^ m' * x) = r ^ m' * (x * r ^ m' * x) := by group
      _ = 1 := by
        have h2 : x * r ^ m' * x = r ^ (-(m' : ℤ)) := by
          simpa using h1
        rw [h2]; simp
  · have h1 := hconj (m' : ℤ)
    have h2 : x * (r ^ m' * x) = (r ^ m')⁻¹ := by
      calc x * (r ^ m' * x) = x * r ^ m' * x := by group
        _ = r ^ (-(m' : ℤ)) := by simpa using h1
        _ = (r ^ m')⁻¹ := by simp
    rw [h2, orderOf_inv, orderOf_pow_of_dvd hm'pos.ne' ⟨4, by omega⟩, hm']
    exact Nat.mul_div_cancel 4 hm'pos
  · have h1 := hconj (m' : ℤ)
    have h2 : x * (r ^ m' * x) = (r ^ m')⁻¹ := by
      calc x * (r ^ m' * x) = x * r ^ m' * x := by group
        _ = r ^ (-(m' : ℤ)) := by simpa using h1
        _ = (r ^ m')⁻¹ := by simp
    rw [h2, hm', show 4 * m' / 2 = 2 * m' by omega]
    have h3 : r ^ (2 * m') * r ^ (2 * m') = 1 := by
      rw [← pow_add, show 2 * m' + 2 * m' = 4 * m' by ring, hrpow]
    rw [inv_pow, show ((r ^ m') ^ 2)⁻¹ = (r ^ (2 * m'))⁻¹ by rw [← pow_mul]; ring_nf]
    exact inv_eq_of_mul_eq_one_right h3
  · rcases Nat.even_or_odd' m' with ⟨j, hj | hj⟩
    · refine ⟨r ^ j, hD j, Or.inl ?_⟩
      have h1 : x * r ^ (-(j : ℤ)) * x = r ^ j := by simpa using hconj (-(j : ℤ))
      have h2 : (r ^ j)⁻¹ = r ^ (-(j : ℤ)) := by simp
      rw [h2]
      calc r ^ m' * x = r ^ j * r ^ j * x := by rw [hj, two_mul, pow_add]
        _ = r ^ j * (x * r ^ (-(j : ℤ)) * x) * x := by rw [h1]
        _ = r ^ j * x * r ^ (-(j : ℤ)) * (x * x) := by group
        _ = r ^ j * x * r ^ (-(j : ℤ)) := by rw [hx, mul_one]
    · refine ⟨r ^ (j + 1), hD (j + 1), Or.inr ?_⟩
      have h1 : x * r ^ (-(j : ℤ)) * x = r ^ j := by simpa using hconj (-(j : ℤ))
      have h2 : (r ^ (j + 1))⁻¹ = r ^ (-((j : ℤ) + 1)) := by
        rw [← zpow_natCast, ← zpow_neg]; push_cast; rfl
      rw [h2, hyx]
      calc r ^ m' * x = r ^ (j + 1) * r ^ j * x := by
            rw [hj, show 2 * j + 1 = (j + 1) + j by ring, pow_add]
        _ = r ^ (j + 1) * (x * r ^ (-(j : ℤ)) * x) * x := by rw [h1]
        _ = r ^ (j + 1) * x * r ^ (-(j : ℤ)) * (x * x) := by group
        _ = r ^ (j + 1) * (x * r) * r ^ (-((j : ℤ) + 1)) := by
            rw [hx, mul_one]; group

theorem smith_1_11_iff {Q Z : Subgroup G} {x : G} (hxZ : ∀ z ∈ Z, x * z * x⁻¹ = z) :
    (∀ q ∈ Q, q * x * q⁻¹ ∈ (fun z => x * z) '' (Z : Set G) → q * x * q⁻¹ = x) ↔
      (∀ q ∈ Q, ⁅q, x⁆ ∈ Z → ⁅q, x⁆ = 1) := by
  have key : ∀ q : G, ⁅q, x⁆ ∈ Z → q * x * q⁻¹ = x * ⁅q, x⁆ := by
    intro q hq
    have h1 := hxZ _ hq
    rw [commutatorElement_def] at h1 ⊢
    calc q * x * q⁻¹ = (q * x * q⁻¹ * x⁻¹) * x := by group
      _ = x * (x⁻¹ * (q * x * q⁻¹ * x⁻¹) * x) := by group
      _ = x * (q * x * q⁻¹ * x⁻¹) := by
        congr 1
        calc x⁻¹ * (q * x * q⁻¹ * x⁻¹) * x = x⁻¹ * (x * (q * x * q⁻¹ * x⁻¹) * x⁻¹) * x := by
              rw [h1]
          _ = q * x * q⁻¹ * x⁻¹ := by group
  constructor
  · intro h q hq hqZ
    have := h q hq ⟨⁅q, x⁆, hqZ, (key q hqZ).symm⟩
    rw [key q hqZ] at this
    simpa using this
  · intro h q hq ⟨z, hz, hzq⟩
    have hzq' : x * z = q * x * q⁻¹ := hzq
    have hqz : ⁅q, x⁆ = z := by
      rw [commutatorElement_def, ← hzq']
      exact hxZ z hz
    have h1 : ⁅q, x⁆ = 1 := h q hq (hqz ▸ hz)
    have hz1 : z = 1 := hqz.symm.trans h1
    rw [← hzq', hz1, mul_one]

end CFSG.RankThree.GF2n.Smith81
