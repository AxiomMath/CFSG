module

public import CFSG.RankThree.GF2n.Smith81.S81R213Basic
public import CFSG.RankThree.GF2n.Smith81.S81LV0
public import CFSG.RankThree.GF2n.Smith81.S81RPure

public section

namespace CFSG.RankThree.GF2n.Smith81.E3LRoot

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.A5Cube CFSG.RankThree.GF2n.Smith81.E3LBridge
  CFSG.RankThree.GF2n.Smith81.E3LCond CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G]

section CaseQ

variable [Finite G] {M Q Z B : Subgroup G} {K : Type} [Field K]
  [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ψ : M₀.E ≃ₗ[K] Cube K}
  {φ : Lgen M (LB M Q B) →* (Cube K ≃ₗ[K] Cube K)} {z : G}

theorem cube_neg_eq_self (v : Cube K) : -v = v := by
  have h2 : (2 : K) • v = 0 := by rw [CharTwo.two_eq_zero, zero_smul]
  rw [two_smul] at h2
  exact neg_eq_of_add_eq_zero_left h2

theorem concl_Q_left (Dt : E3LDat M Q Z B K γ M₀ ψ φ z) {x y : G} (hxc : IsConj z x)
    (hxQ : x ∈ Q) (hyc : IsConj z y) (hyM : y ∈ M) (hyQ : y ∉ Q) :
    (orderOf (x * y) = 2 ∨ orderOf (x * y) = 4 ∨ Odd (orderOf (x * y))) ∧
      (orderOf (x * y) = 4 → InZClass Z ((x * y) ^ 2)) := by
  have H : StrothHyp M Q Z := Dt.ctx.hyp
  obtain ⟨gy, hgy, hy⟩ := Dt.actsAs hyc hyM hyQ
  have hyL : y ∈ Lgen M (LB M Q B) := hy.mem_Lgen
  have hyy : y * y = 1 := mul_self_eq_one_of_isConj_Z H Dt.hz hyc
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hyxQ : y * x * y⁻¹ ∈ Q := conj_mem_Q H hyM hxQ
  have hcQ : x * (y * x * y⁻¹) ∈ Q := Q.mul_mem hxQ hyxQ
  have hsq2 : (x * y) ^ 2 = x * (y * x * y⁻¹) := by rw [pow_two, hyinv]; group
  have hψc : ψ (M₀.π (x * (y * x * y⁻¹))) = (rho K gy - 1) (ψ (M₀.π x)) := by
    rw [M₀.π_mul x hxQ _ hyxQ]
    have hev := Dt.d.equivariant ⟨y, hyL⟩ x hxQ
    rw [hy.phi hyL] at hev
    simp only [map_add, rhoEquiv_apply] at hev ⊢
    rw [show ψ (M₀.π (y * x * y⁻¹)) = rho K gy (ψ (M₀.π x)) from hev]
    simp only [LinearMap.sub_apply, Module.End.one_apply]
    rw [sub_eq_add_neg, add_comm, cube_neg_eq_self]
  have hp : IsPure K (ψ (M₀.π x)) := by
    by_cases hxZ : x ∈ Z
    · rw [(M₀.π_ker x hxQ).mpr hxZ, map_zero]
      exact isPure_zero
    · exact Dt.d.isPure_of_isConj H Dt.hz hxc hxQ hxZ
  have hpure : IsPure K (ψ (M₀.π (x * (y * x * y⁻¹)))) := by
    rw [hψc]
    exact isPure_rho_sub_one hgy hp
  have hcl : (x * y) ^ 2 = 1 ∨ InZClass Z ((x * y) ^ 2) := by
    rw [hsq2]
    by_cases h0 : M₀.π (x * (y * x * y⁻¹)) = 0
    · have hcZ : x * (y * x * y⁻¹) ∈ Z := (M₀.π_ker _ hcQ).mp h0
      by_cases hc1 : x * (y * x * y⁻¹) = 1
      · exact Or.inl hc1
      · exact Or.inr ⟨1, _, hcZ, hc1, by group⟩
    · have hcZ : x * (y * x * y⁻¹) ∉ Z := fun h => h0 ((M₀.π_ker _ hcQ).mpr h)
      have hconj := Dt.d.isConj_of_isPure H Dt.hD Dt.hz Dt.hz1 hcQ hcZ hpure
      exact Or.inr (inZClass_of_isConj Dt.hz Dt.hz1 hconj)
  have hsqsq : ((x * y) ^ 2) * ((x * y) ^ 2) = 1 := by
    rcases hcl with h | h
    · rw [h, one_mul]
    · exact InZClass.mul_self H h
  refine lin213_of_pow_four (by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_two]; exact hsqsq) fun hne => ?_
  rcases hcl with h | h
  · exact absurd h hne
  · exact h

end CaseQ

end CFSG.RankThree.GF2n.Smith81.E3LRoot
