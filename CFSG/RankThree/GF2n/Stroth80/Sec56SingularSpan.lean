module

public import CFSG.ClassicalGroups.Orthogonal.InvariantPairing
public import CFSG.RankThree.GF2n.Stroth80.Sec7Om4NonsingStab

public section

namespace CFSG.ClassicalGroups.Orthogonal

open QuadraticMap

private theorem polar_self_eq_zero_of_charTwo {K V : Type} [Field K] [CharP K 2]
    [AddCommGroup V] [Module K V] (Q : QuadraticForm K V) (x : V) : polar Q x x = 0 := by
  rw [polar_self, CharTwo.two_nsmul]

private theorem polar_smul_add_of_polar_eq_zero {K V : Type} [Field K] [CharP K 2]
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {d y : V} (l : K)
    (hy : polar Q d y = 0) : polar Q d (l • d + y) = 0 := by
  rw [polar_add_right, polar_smul_right, polar_self_eq_zero_of_charTwo, smul_zero, zero_add, hy]

private theorem polar_smul_add_smul_add {K V : Type} [Field K] [CharP K 2] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} {d u v : V} (l m : K) (hu : polar Q d u = 0)
    (hv : polar Q d v = 0) : polar Q (l • d + u) (m • d + v) = polar Q u v := by
  have hu' : polar Q u d = 0 := by rw [polar_comm]; exact hu
  simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right,
    polar_self_eq_zero_of_charTwo, hu, hv, hu', smul_zero, zero_add, add_zero]

private theorem exists_singular_lift_mem {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {S : AddSubgroup V} {d y : V}
    (hS : ∀ s : V, polar Q d s = 0 → Q s = 0 → s ∈ S) (hd : Q d ≠ 0)
    (hy : polar Q d y = 0) : ∃ l : K, l • d + y ∈ S ∧ Q (l • d + y) = 0 := by
  obtain ⟨l, hl⟩ := CFSG.RankThree.GF2n.Stroth80.sec7ns_singular_lift hd hy
  exact ⟨l, hS _ (polar_smul_add_of_polar_eq_zero l hy) hl, hl⟩

theorem mem_of_forall_singular_perp {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] [Finite K] [CharP K 2] {Q' : QuadraticForm K (ι → K)}
    (hQ : (QuadraticMap.polarBilin Q').Nondegenerate) (h3 : 3 ≤ Module.finrank K (ι → K))
    {d : ι → K} (hd : Q' d ≠ 0) {S : AddSubgroup (ι → K)}
    (hS : ∀ s : ι → K, QuadraticMap.polar Q' d s = 0 → Q' s = 0 → s ∈ S)
    {x : ι → K} (hx : QuadraticMap.polar Q' d x = 0) : x ∈ S := by
  have hd0 : d ≠ 0 := fun h => hd (by simp [h])
  have hmul : ∀ μ : K, μ • d ∈ S := by
    intro μ
    obtain ⟨a, b, ha, hb, hab⟩ := exists_perp_pair_polar_ne_zero hQ h3 hd0
    obtain ⟨c, hc⟩ : ∃ c : K, c * polar Q' a b = μ * μ * Q' d :=
      ⟨μ * μ * Q' d / polar Q' a b, div_mul_cancel₀ _ hab⟩
    have ha' : polar Q' d (c • a) = 0 := by rw [polar_smul_right, ha, smul_zero]
    have hab' : polar Q' (c • a) b = μ * μ * Q' d := by
      rw [polar_smul_left, smul_eq_mul, hc]
    have habs : polar Q' d (c • a + b) = 0 := by
      rw [polar_add_right, ha', hb, add_zero]
    obtain ⟨l₁, hs₁, hq₁⟩ := exists_singular_lift_mem hS hd ha'
    obtain ⟨l₂, hs₂, hq₂⟩ := exists_singular_lift_mem hS hd hb
    obtain ⟨l₃, hs₃, hq₃⟩ := exists_singular_lift_mem hS hd habs
    have hX : polar Q' (l₃ • d + (c • a + b)) d = 0 := by
      rw [polar_comm]
      exact polar_smul_add_of_polar_eq_zero l₃ habs
    have e1 : Q' ((l₁ • d + c • a) + (l₂ • d + b)) = μ * μ * Q' d := by
      rw [QuadraticMap.map_add Q' _ _, hq₁, hq₂, zero_add, zero_add,
        polar_smul_add_smul_add l₁ l₂ ha' hb, hab']
    have e2 : Q' ((l₃ • d + (c • a + b)) + (l₁ + l₂ - l₃) • d) =
        (l₁ + l₂ - l₃) * (l₁ + l₂ - l₃) * Q' d := by
      rw [QuadraticMap.map_add Q' _ _, hq₃, zero_add, polar_smul_right, hX, smul_zero,
        add_zero, QuadraticMap.map_smul, smul_eq_mul]
    have e3 : (l₁ • d + c • a) + (l₂ • d + b) =
        (l₃ • d + (c • a + b)) + (l₁ + l₂ - l₃) • d := by
      module
    have e4 : μ * μ * Q' d = (l₁ + l₂ - l₃) * (l₁ + l₂ - l₃) * Q' d := by
      rw [← e1, e3, e2]
    have e5 : μ * μ = (l₁ + l₂ - l₃) * (l₁ + l₂ - l₃) := mul_right_cancel₀ hd e4
    have e6 : μ = l₁ + l₂ - l₃ := by
      have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
      have hsq : (μ - (l₁ + l₂ - l₃)) * (μ - (l₁ + l₂ - l₃)) = 0 := by
        linear_combination e5 + ((l₁ + l₂ - l₃) * (l₁ + l₂ - l₃) - μ * (l₁ + l₂ - l₃)) * h2
      exact sub_eq_zero.mp (mul_self_eq_zero.mp hsq)
    have hνd : (l₁ • d + c • a) + (l₂ • d + b) - (l₃ • d + (c • a + b)) =
        (l₁ + l₂ - l₃) • d := by
      module
    have hmem := S.sub_mem (S.add_mem hs₁ hs₂) hs₃
    rw [hνd] at hmem
    rw [e6]
    exact hmem
  obtain ⟨l, hs, -⟩ := exists_singular_lift_mem hS hd hx
  simpa using S.sub_mem hs (hmul l)

end CFSG.ClassicalGroups.Orthogonal
