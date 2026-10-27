module

public import CFSG.RankThree.PartTwo.Sec11.WreathFacts

public section

namespace CFSG.RankThree.PartTwo.Sec11.Item1119Sym

theorem pow_three_mem_of_abelian_normal {P : Type*} [Group P] {K : Subgroup P} [K.Normal]
    (e : P ⧸ K ≃* W33) (V : Subgroup P)
    (hVn : ∀ p : P, ∀ v ∈ V, p * v * p⁻¹ ∈ V)
    (hV : ∀ u ∈ V, ∀ v ∈ V, u * v * u⁻¹ * v⁻¹ ∈ K) : ∀ v ∈ V, v ^ 3 ∈ K := by
  let π : P →* W33 := e.toMonoidHom.comp (QuotientGroup.mk' K)
  have hπapp : ∀ p : P, π p = e (p : P ⧸ K) := fun p => rfl
  have hπsurj : Function.Surjective π := by
    intro w
    obtain ⟨p, hp⟩ := QuotientGroup.mk_surjective (e.symm w)
    exact ⟨p, by rw [hπapp, hp, MulEquiv.apply_symm_apply]⟩
  have hπK : ∀ k ∈ K, π k = 1 := by
    intro k hk
    rw [hπapp, (QuotientGroup.eq_one_iff k).mpr hk, map_one]
  have hNn : (V.map π).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hn
    obtain ⟨p, rfl⟩ := hπsurj g
    exact Subgroup.mem_map.mpr ⟨p * v * p⁻¹, hVn p v hv, by simp only [map_mul, map_inv]⟩
  have hab : ∀ x ∈ V.map π, ∀ y ∈ V.map π, x * y = y * x := by
    intro x hx y hy
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hy
    have h1 : π (u * v * u⁻¹ * v⁻¹) = 1 := hπK _ (hV u hu v hv)
    simp only [map_mul, map_inv] at h1
    have h2 : π u * π v * (π u)⁻¹ = π v := mul_inv_eq_one.mp h1
    calc π u * π v = π u * π v * (π u)⁻¹ * π u := by group
      _ = π v * π u := by rw [h2]
  intro v hv
  have h3 := pow_three_eq_one_of_abelian_normal hNn hab (π v) (Subgroup.mem_map_of_mem π hv)
  have h3' : π (v ^ 3) = 1 := by rw [map_pow]; exact h3
  have h4 : ((v ^ 3 : P) : P ⧸ K) = 1 := by
    apply e.injective
    rw [← hπapp, h3', map_one]
  exact (QuotientGroup.eq_one_iff (v ^ 3)).mp h4

end CFSG.RankThree.PartTwo.Sec11.Item1119Sym

end
