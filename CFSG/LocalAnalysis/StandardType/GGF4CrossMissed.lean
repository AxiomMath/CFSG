module

public import CFSG.LocalAnalysis.StandardType.GGF4OrbCore
public import CFSG.LocalAnalysis.StandardType.GGF4Rk2Core
import CFSG.LocalAnalysis.StandardType.GGF4RankFour
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType.F4Model

namespace F4Rep

variable {W : Type} [Group W] (R : F4Rep W)

theorem isLongM_iff_of_conj_eq {g h : W} {i j : Fin 4}
    (e : g * R.s i * g⁻¹ = h * R.s j * h⁻¹) : IsLongM (Sm i) ↔ IsLongM (Sm j) := by
  obtain ⟨x, hx, hρ⟩ := R.refl_rep ⟨h, j, rfl⟩
  exact (R.isLongM_of_conj g i hx (by rw [e]; exact hρ)).symm.trans (R.isLongM_of_conj h j hx hρ)

theorem conj_of_orderOf_eq_three {x y : W} (hx : x * x = 1) (hy : y * y = 1)
    (h : orderOf (x * y) = 3) : (x * y) * x * (x * y)⁻¹ = y := by
  have h3 : (x * y) ^ 3 = 1 := by rw [← h]; exact pow_orderOf_eq_one _
  rw [pow_three] at h3
  have h3' : x * y * x * y * x * y = 1 := by simpa only [mul_assoc] using h3
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hy]
  calc x * y * x * (y * x) = (x * y * x * y * x * y) * y⁻¹ := by group
    _ = y := by rw [h3', one_mul, inv_eq_of_mul_eq_one_right hy]

theorem exists_conj_zero_of_lt_two {a : Fin 3 → W} (ha : ∀ k, R.IsRefl (a k))
    (ha01 : orderOf (a 0 * a 1) = 3) {c : Fin 3} (hc : c.val < 2) :
    ∃ g : W, g * a 0 * g⁻¹ = a c := by
  fin_cases c
  · exact ⟨1, by rw [one_mul, inv_one, mul_one]; rfl⟩
  · exact ⟨a 0 * a 1, conj_of_orderOf_eq_three (ha 0).mul_self (ha 1).mul_self ha01⟩
  · exact absurd hc (by decide)

theorem not_conj_zero_two {a : Fin 3 → W} (ha : ∀ k, R.IsRefl (a k))
    (ha01 : orderOf (a 0 * a 1) = 3) (ha12 : orderOf (a 1 * a 2) = 4)
    (ha02 : orderOf (a 0 * a 2) = 2) (h : W) : h * a 0 * h⁻¹ ≠ a 2 := by
  intro e
  obtain ⟨g, hg⟩ := R.classify (ha 0) (ha 1) (ha 2) ha01 ha12 ha02
  rcases hg with ⟨h0, -, h2⟩ | ⟨h0, -, h2⟩
  · have e' : (g * h * g⁻¹) * R.s 0 * (g * h * g⁻¹)⁻¹ = 1 * R.s 2 * 1⁻¹ := by
      rw [← h0, ← h2, ← e]
      group
    exact absurd (R.isLongM_iff_of_conj_eq e') (by decide)
  · have e' : (g * h * g⁻¹) * R.s 3 * (g * h * g⁻¹)⁻¹ = 1 * R.s 1 * 1⁻¹ := by
      rw [← h0, ← h2, ← e]
      group
    exact absurd (R.isLongM_iff_of_conj_eq e') (by decide)

theorem exists_missed_cross {a b : Fin 3 → W} (ha : ∀ k, R.IsRefl (a k))
    (ha01 : orderOf (a 0 * a 1) = 3) (ha12 : orderOf (a 1 * a 2) = 4)
    (ha02 : orderOf (a 0 * a 2) = 2) (hb : ∀ k, R.IsRefl (b k))
    (hb01 : orderOf (b 0 * b 1) = 3) (hb12 : orderOf (b 1 * b 2) = 4)
    (hb02 : orderOf (b 0 * b 2) = 2)
    (hgen : Subgroup.closure (Set.range a) ⊔ Subgroup.closure (Set.range b) = ⊤)
    {g₀ : W} (h0 : g₀ * a 0 * g₀⁻¹ = b 0) :
    ∃ (w : W) (i j : Fin 4), CoxeterMatrix.F₄ i j = 3 ∧
      w * R.s i * w⁻¹ ∈ Subgroup.closure (Set.range a) ∧
      w * R.s j * w⁻¹ ∈ Subgroup.closure (Set.range b) ∧
      (∃ h : W, h * R.s j * h⁻¹ = b 2) ∧ ∀ h : W, h * a 0 * h⁻¹ ≠ R.s i := by
  obtain ⟨g, hg⟩ := R.classify (ha 0) (ha 1) (ha 2) ha01 ha12 ha02
  obtain ⟨h, hh⟩ := R.classify (hb 0) (hb 1) (hb 2) hb01 hb12 hb02
  have e23 : R.wd [2, 3] * R.s 2 * (R.wd [2, 3])⁻¹ = R.s 3 :=
    R.conj_wd_eq (R.hs 2) (R.hs 3) (by decide)
  have e01 : R.wd [0, 1] * R.s 0 * (R.wd [0, 1])⁻¹ = R.s 1 :=
    R.conj_wd_eq (R.hs 0) (R.hs 1) (by decide)
  rcases hg with ⟨ga0, ga1, ga2⟩ | ⟨ga0, ga1, ga2⟩ <;>
    rcases hh with ⟨hb0', hb1', hb2'⟩ | ⟨hb0', hb1', hb2'⟩
  ·
    obtain ⟨w, hw2, hw3⟩ := R.exists_cross_of_B ⟨ga0, ga1, ga2⟩ hb hgen
    refine ⟨w, 2, 3, by decide, hw2, hw3, ⟨h⁻¹ * (R.wd [2, 3])⁻¹, ?_⟩, fun k e => ?_⟩
    · have hb2 : b 2 = h⁻¹ * R.s 2 * h := by rw [← hb2']; group
      rw [hb2, ← e23]
      group
    · have e' : (k * g⁻¹) * R.s 0 * (k * g⁻¹)⁻¹ = 1 * R.s 2 * 1⁻¹ := by
        rw [← ga0, ← e]
        group
      exact absurd (R.isLongM_iff_of_conj_eq e') (by decide)
  ·
    exfalso
    have e' : (h * g₀ * g⁻¹) * R.s 0 * (h * g₀ * g⁻¹)⁻¹ = 1 * R.s 3 * 1⁻¹ := by
      rw [← ga0, ← hb0', ← h0]
      group
    exact absurd (R.isLongM_iff_of_conj_eq e') (by decide)
  ·
    exfalso
    have e' : (h * g₀ * g⁻¹) * R.s 3 * (h * g₀ * g⁻¹)⁻¹ = 1 * R.s 0 * 1⁻¹ := by
      rw [← ga0, ← hb0', ← h0]
      group
    exact absurd (R.isLongM_iff_of_conj_eq e') (by decide)
  ·
    obtain ⟨w, hw1, hw0⟩ := R.exists_cross_of_C ⟨ga0, ga1, ga2⟩ hb hgen
    refine ⟨w, 1, 0, by decide, hw1, hw0, ⟨h⁻¹ * R.wd [0, 1], ?_⟩, fun k e => ?_⟩
    · have hb2 : b 2 = h⁻¹ * R.s 1 * h := by rw [← hb2']; group
      rw [hb2, ← e01]
      group
    · have e' : (k * g⁻¹) * R.s 3 * (k * g⁻¹)⁻¹ = 1 * R.s 1 * 1⁻¹ := by
        rw [← ga0, ← e]
        group
      exact absurd (R.isLongM_iff_of_conj_eq e') (by decide)

theorem not_pair_mem_of_not_conj {a : Fin 3 → W} (ha : ∀ k, R.IsRefl (a k))
    (ha01 : orderOf (a 0 * a 1) = 3) (ha12 : orderOf (a 1 * a 2) = 4)
    (ha02 : orderOf (a 0 * a 2) = 2) {i j : Fin 4} (hij3 : CoxeterMatrix.F₄ i j = 3)
    (hord : orderOf (R.s i * R.s j) = CoxeterMatrix.F₄ i j)
    (hi : ∀ h : W, h * a 0 * h⁻¹ ≠ R.s i) (w' : W)
    (h1 : w' * R.s i * w'⁻¹ ∈ Subgroup.closure (Set.range a)) :
    w' * R.s j * w'⁻¹ ∉ Subgroup.closure (Set.range a) := by
  intro h2
  have hij : i ≠ j := by
    rintro rfl
    rw [CoxeterMatrix.diagonal] at hij3
    exact absurd hij3 (by decide)
  obtain ⟨v, c, d, e1, -, -, h3, -⟩ := R.pair_core ha ha01 ha12 ha02 hij hord h1 h2
  obtain ⟨rfl, -⟩ := h3 hij3
  apply hi (w'⁻¹ * (v.map a).prod)
  rw [show w'⁻¹ * (v.map a).prod * a 0 * (w'⁻¹ * (v.map a).prod)⁻¹ =
      w'⁻¹ * ((v.map a).prod * a 0 * ((v.map a).prod)⁻¹) * w' by group, ← e1]
  group

end F4Rep

end CFSG.StandardType.F4Model

end
