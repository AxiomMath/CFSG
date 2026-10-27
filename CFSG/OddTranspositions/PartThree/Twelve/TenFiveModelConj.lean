module

public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveModelWalk

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix

open FiveWalk

theorem isConj_of_pairing_ne {k : ℕ} (hk : 4 ≤ k) (ε π : Bool) {x y : Fin (k + 1) → ZMod 5}
    (hx : fiveForm k ε x x ≠ 0) (hxπ : IsSquare (fiveForm k ε x x) ↔ π = true)
    (hy : fiveForm k ε y y ≠ 0) (hyπ : IsSquare (fiveForm k ε y y) ↔ π = true)
    (hQ : fiveForm k ε y y = fiveForm k ε x x) (hb : fiveForm k ε x y ≠ 0) :
    ∃ g ∈ fiveReflectionGroup k ε π, g * fiveReflOf k ε x * g⁻¹ = fiveReflOf k ε y := by
  rcases five_sq_class_same (fiveForm k ε x x) (fiveForm k ε x y) hx hb with
    ⟨hu_ne, husq⟩ | ⟨hu_ne, husq⟩
  ·
    have huQ : fiveForm k ε (x - y) (x - y) = 2 * fiveForm k ε x x - 2 * fiveForm k ε x y := by
      rw [fiveNorm_sub, hQ]; ring
    have husign : IsSquare (fiveForm k ε (x - y) (x - y)) ↔ π = true := by
      rw [huQ]; exact husq.trans hxπ
    refine ⟨fiveReflOf k ε (x - y), Subgroup.subset_closure (fiveReflOf_mem (by rw [huQ]; exact hu_ne)
      husign), ?_⟩
    have htx : (((fiveReflOf k ε (x - y) : GL (Fin (k + 1)) (ZMod 5)) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x) = y :=
      fiveReflOf_sub_mulVec k ε hQ (by rwa [huQ])
    rw [conj_fiveReflOf (hg := fiveForm_fiveReflOf k ε (x - y)) x, htx]
  ·
    have huQ : fiveForm k ε (x + y) (x + y) = 2 * fiveForm k ε x x + 2 * fiveForm k ε x y := by
      rw [fiveNorm_add, hQ]; ring
    have husign : IsSquare (fiveForm k ε (x + y) (x + y)) ↔ π = true := by
      rw [huQ]; exact husq.trans hxπ
    refine ⟨fiveReflOf k ε (x + y), Subgroup.subset_closure (fiveReflOf_mem (by rw [huQ]; exact hu_ne)
      husign), ?_⟩
    have htx : (((fiveReflOf k ε (x + y) : GL (Fin (k + 1)) (ZMod 5)) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x) = -y :=
      fiveReflOf_add_mulVec k ε hQ (by rwa [huQ])
    rw [conj_fiveReflOf (hg := fiveForm_fiveReflOf k ε (x + y)) x, htx]
    exact fiveReflOf_neg k ε y

theorem isConj_of_pairing_eq_zero {k : ℕ} (hk : 4 ≤ k) (ε π : Bool)
    {x y : Fin (k + 1) → ZMod 5}
    (hx : fiveForm k ε x x ≠ 0) (hxπ : IsSquare (fiveForm k ε x x) ↔ π = true)
    (hy : fiveForm k ε y y ≠ 0) (hyπ : IsSquare (fiveForm k ε y y) ↔ π = true)
    (hQ : fiveForm k ε y y = fiveForm k ε x x) (hb : fiveForm k ε x y = 0) :
    ∃ g ∈ fiveReflectionGroup k ε π, g * fiveReflOf k ε x * g⁻¹ = fiveReflOf k ε y := by
  obtain ⟨w, hwx, hwy, hwQ⟩ :=
    exists_fiveForm_orth_eq hk ε hx y (d := -fiveForm k ε x x) (neg_ne_zero.mpr hx)
  have hxw : fiveForm k ε x w = 0 := by rw [fiveForm_comm k ε x w]; exact hwx
  have hyw : fiveForm k ε y w = 0 := by rw [fiveForm_comm k ε y w]; exact hwy
  have hxy : fiveForm k ε (x + y) (x + y) = 2 * fiveForm k ε x x := by
    rw [fiveNorm_add, hQ, hb]; ring
  have hbw : fiveForm k ε (x + y) w = 0 := by
    rw [fiveForm_add_left, hxw, hyw, add_zero]
  have hQz : fiveForm k ε ((x + y) + w) ((x + y) + w) = fiveForm k ε x x := by
    rw [fiveNorm_add, hxy, hwQ, hbw, two_mul]
    abel
  have hxz : fiveForm k ε x ((x + y) + w) = fiveForm k ε x x := by
    rw [fiveForm_add_right, fiveForm_add_right, hxw, hb]; ring
  have hzy : fiveForm k ε ((x + y) + w) y = fiveForm k ε x x := by
    rw [fiveForm_add_left, fiveForm_add_left, hb, hQ, hwy]; ring
  obtain ⟨g₁, hg₁, hc₁⟩ := isConj_of_pairing_ne hk ε π hx hxπ (by rw [hQz]; exact hx)
    (by rw [hQz]; exact hxπ) hQz (by rw [hxz]; exact hx)
  obtain ⟨g₂, hg₂, hc₂⟩ := isConj_of_pairing_ne hk ε π (by rw [hQz]; exact hx)
    (by rw [hQz]; exact hxπ) hy hyπ (hQ.trans hQz.symm) (by rw [hzy]; exact hx)
  refine ⟨g₂ * g₁, Subgroup.mul_mem _ hg₂ hg₁, ?_⟩
  calc g₂ * g₁ * fiveReflOf k ε x * (g₂ * g₁)⁻¹
      = g₂ * (g₁ * fiveReflOf k ε x * g₁⁻¹) * g₂⁻¹ := by group
    _ = fiveReflOf k ε y := by rw [hc₁, hc₂]

theorem isConj_of_mem_fiveReflections_aux {k : ℕ} (hk : 4 ≤ k) (ε π : Bool)
    {r s : GL (Fin (k + 1)) (ZMod 5)} (hr : r ∈ fiveReflections k ε π)
    (hs : s ∈ fiveReflections k ε π) :
    ∃ g ∈ fiveReflectionGroup k ε π, g * r * g⁻¹ = s := by
  obtain ⟨x, hx, hxπ, rfl⟩ := exists_eq_fiveReflOf hr
  obtain ⟨y, hy, hyπ, rfl⟩ := exists_eq_fiveReflOf hs
  obtain ⟨l, hl⟩ := exists_sq_mul_eq_of_isSquare_iff hy hx (hyπ.trans hxπ.symm)
  have hl0 : l ≠ 0 := by
    have hne : l ^ 2 * fiveForm k ε y y ≠ 0 := by rw [hl]; exact hx
    rintro rfl
    exact hne (by norm_num)
  have hQy : fiveForm k ε (l • y) (l • y) = fiveForm k ε x x := by
    rw [fiveForm_smul_left, fiveForm_smul_right,
      show l * (l * fiveForm k ε y y) = l ^ 2 * fiveForm k ε y y by ring, hl]
  have hy' : fiveForm k ε (l • y) (l • y) ≠ 0 := by rw [hQy]; exact hx
  have hy'π : IsSquare (fiveForm k ε (l • y) (l • y)) ↔ π = true := by rw [hQy]; exact hxπ
  rw [← fiveReflOf_smul k ε y hl0]
  by_cases hb : fiveForm k ε x (l • y) = 0
  · exact isConj_of_pairing_eq_zero hk ε π hx hxπ hy' hy'π hQy hb
  · exact isConj_of_pairing_ne hk ε π hx hxπ hy' hy'π hQy hb

end CFSG.OddTranspositions.PartThree
