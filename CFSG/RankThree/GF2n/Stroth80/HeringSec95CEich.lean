module

public import CFSG.ClassicalGroups.Orthogonal.RootGroupCard
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.ClassicalGroups.Orthogonal QuadraticMap

namespace HS9

variable {K : Type} [Field K] [CharP K 2] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q' : QuadraticForm K (ι → K)}

theorem eichler_sub_apply {u w : ι → K} (hu : Q' u = 0) (hw : polar Q' u w = 0) (hQw : Q' w = 0)
    (x : ι → K) :
    eichler Q' u w x - x = polar Q' x u • w + polar Q' x w • u := by
  rw [eichler_apply hu hw, hQw, zero_mul, add_zero]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  funext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-(polar Q' x w * u i)) * h2

theorem polar_eichler_self_char2 {u w : ι → K} (hu : Q' u = 0) (hw : polar Q' u w = 0)
    (y : ι → K) : polar Q' y (eichler Q' u w y) = Q' w * polar Q' y u ^ 2 := by
  rw [polar_apply_eichler_self hu hw]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination (Q' y - Q' w * polar Q' y u ^ 2) * h2

theorem map_comb_eq_zero {u w : ι → K} (hu : Q' u = 0) (hw : polar Q' u w = 0) (hQw : Q' w = 0)
    (α β : K) : Q' (α • u + β • w) = 0 := by
  rw [QuadraticMap.map_add Q' (α • u) (β • w), map_smul_eq_sq, map_smul_eq_sq,
    polar_smul_left_eq, polar_smul_right_eq, hu, hQw, hw]
  simp

theorem exists_polar_ne_zero (hQ : (polarBilin Q').Nondegenerate) {u : ι → K} (hu0 : u ≠ 0) :
    ∃ y, polar Q' y u ≠ 0 := by
  by_contra h
  push Not at h
  exact hu0 (hQ.2 u fun x => by simpa using h x)

theorem exists_polar_eq_one (hQ : (polarBilin Q').Nondegenerate) {u : ι → K} (hu0 : u ≠ 0) :
    ∃ y, polar Q' y u = 1 := by
  obtain ⟨y, hy⟩ := exists_polar_ne_zero hQ hu0
  exact ⟨(polar Q' y u)⁻¹ • y, by rw [polar_smul_left_eq, inv_mul_cancel₀ hy]⟩

theorem exists_polar_pair (hQ : (polarBilin Q').Nondegenerate) {u w : ι → K} (hu0 : u ≠ 0)
    (hind : ∀ c : K, w ≠ c • u) : ∃ y, polar Q' y u = 0 ∧ polar Q' y w = 1 := by
  obtain ⟨y₀, hy₀⟩ := exists_polar_eq_one hQ hu0
  have hex : ∃ y, polar Q' y u = 0 ∧ polar Q' y w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hind (polar Q' y₀ w)
    refine sub_eq_zero.mp (hQ.2 _ fun y => ?_)
    have h1 : polar Q' (y - polar Q' y u • y₀) u = 0 := by
      rw [polar_sub_left, polar_smul_left_eq, hy₀, mul_one, sub_self]
    have h2 := hcon _ h1
    rw [polar_sub_left, polar_smul_left_eq, sub_eq_zero] at h2
    simpa [polar_sub_right, polar_smul_right_eq, mul_comm] using sub_eq_zero.mpr h2
  obtain ⟨y, hyu, hyw⟩ := hex
  refine ⟨(polar Q' y w)⁻¹ • y, ?_, ?_⟩
  · rw [polar_smul_left_eq, hyu, mul_zero]
  · rw [polar_smul_left_eq, inv_mul_cancel₀ hyw]

theorem eichler_sub_mem {u w : ι → K} (hu : Q' u = 0) (hw : polar Q' u w = 0) (hQw : Q' w = 0)
    (y : ι → K) : ∃ α β : K, eichler Q' u w y - y = α • u + β • w :=
  ⟨polar Q' y w, polar Q' y u, by rw [eichler_sub_apply hu hw hQw, add_comm]⟩

theorem eichler_sub_apply' {u w : ι → K} (hu : Q' u = 0) (hw : polar Q' u w = 0) (x : ι → K) :
    eichler Q' u w x - x =
      polar Q' x u • w - (polar Q' x w + Q' w * polar Q' x u) • u := by
  rw [eichler_apply hu hw]
  abel

theorem eichler_sub_mem' {u w : ι → K} (hu : Q' u = 0) (hw : polar Q' u w = 0)
    (y : ι → K) : ∃ α β : K, eichler Q' u w y - y = α • u + β • w :=
  ⟨-(polar Q' y w + Q' w * polar Q' y u), polar Q' y u, by
    rw [eichler_sub_apply' hu hw]
    module⟩

theorem exists_eichler_sub_eq' (hQ : (polarBilin Q').Nondegenerate) {u w : ι → K}
    (hu : Q' u = 0) (hw : polar Q' u w = 0) (hu0 : u ≠ 0) (hind : ∀ c : K, w ≠ c • u)
    (α β : K) : ∃ y, eichler Q' u w y - y = α • u + β • w := by
  have hw0 : w ≠ 0 := by
    intro h
    exact hind 0 (by rw [h, zero_smul])
  have hind' : ∀ c : K, u ≠ c • w := by
    intro c hc
    by_cases hc0 : c = 0
    · exact hu0 (by rw [hc, hc0, zero_smul])
    · exact hind c⁻¹ (by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul])
  obtain ⟨y₀, hy₀u, hy₀w⟩ := exists_polar_pair hQ hw0 hind'
  obtain ⟨y₁, hy₁u, hy₁w⟩ := exists_polar_pair hQ hu0 hind
  refine ⟨β • y₀ + (-α - Q' w * β) • y₁, ?_⟩
  rw [eichler_sub_apply' hu hw]
  have h1 : polar Q' (β • y₀ + (-α - Q' w * β) • y₁) u = β := by
    rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, hy₀w, hy₁u]
    ring
  have h2 : polar Q' (β • y₀ + (-α - Q' w * β) • y₁) w = -α - Q' w * β := by
    rw [polar_add_left, polar_smul_left_eq, polar_smul_left_eq, hy₀u, hy₁w]
    ring
  rw [h1, h2]
  module

end HS9

end CFSG.RankThree.GF2n.Stroth80
