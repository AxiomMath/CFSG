module

public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtEta
import CFSG.LocalAnalysis.StandardType.ZS.ImpExtF4Refl
import CFSG.LocalAnalysis.StandardType.ZS.RootMatrix
import CFSG.LocalAnalysis.StandardType.ZS.Basic
import CFSG.LocalAnalysis.StandardType.ZS.CommutingRefl

public section

namespace CFSG.StandardType.ZS.FFourCoord

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

theorem etaOK_four_of_dMax (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {G : Subgroup (U ≃ₗ[ZMod p] U)} (hG : DMax p G 4) {a b : U}
    {φ ψ : Module.Dual (ZMod p) U} (hφ : φ a = 2) (hψ : ψ b = 2)
    (ha : Module.reflection hφ ∈ G) (hb : Module.reflection hψ ∈ G)
    (hne : Module.reflection hφ ≠ Module.reflection hψ) : EtaOK 4 (φ b) (ψ a) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  have : Finite U := Module.finite_of_finite (R := ZMod p) (M := U)
  have : Finite (U ≃ₗ[ZMod p] U) :=
    Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U))
      (fun e f h => LinearEquiv.ext (fun x => congrFun h x))
  have hle : orderOf (Module.reflection hφ * Module.reflection hψ) ≤ 4 :=
    hG.1 _ ha _ hb (isRefl_reflection hp hφ) (isRefl_reflection hp hψ)
  have hpos : 0 < orderOf (Module.reflection hφ * Module.reflection hψ) :=
    (isOfFinOrder_of_finite _).orderOf_pos
  have hcases : orderOf (Module.reflection hφ * Module.reflection hψ) = 1 ∨
      orderOf (Module.reflection hφ * Module.reflection hψ) = 2 ∨
      orderOf (Module.reflection hφ * Module.reflection hψ) = 3 ∨
      orderOf (Module.reflection hφ * Module.reflection hψ) = 4 := by omega
  rcases hcases with h1 | h2 | h3 | h4
  · exfalso
    have hone : Module.reflection hφ * Module.reflection hψ = 1 := orderOf_eq_one_iff.mp h1
    refine hne ?_
    rw [eq_inv_of_mul_eq_one_left hone, Module.reflection_inv]
  · exact Or.inl (apply_eq_zero_of_orderOf_eq_two hp hφ hψ h2)
  · exact Or.inr (Or.inl ⟨by norm_num,
      apply_mul_apply_eq_one_of_orderOf_eq_three hp hφ hψ h3⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨by norm_num,
      apply_mul_apply_eq_two_of_orderOf_eq_four hp hφ hψ h4⟩))

theorem etaOK_four_of_toMatrix (hp : p ≠ 2) {G : Subgroup (U ≃ₗ[ZMod p] U)} (hG : DMax p G 4)
    {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod p) U) {x r : U ≃ₗ[ZMod p] U} (hx : x ∈ G) (hr : r ∈ G)
    (hne : x ≠ r) {v w ρ κ : Fin n → ZMod p}
    (hxm : LinearMap.toMatrix f f x.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2)
    (hrm : LinearMap.toMatrix f f r.toLinearMap = 1 - Matrix.vecMulVec ρ κ)
    (hκρ : ∑ i, κ i * ρ i = 2) :
    EtaOK 4 (∑ i, w i * ρ i) (∑ i, κ i * v i) := by
  have : Module.Finite (ZMod p) U := Module.Finite.of_basis f
  obtain ⟨hφ, rfl⟩ := eq_reflection_of_toMatrix f hxm hwv
  obtain ⟨hψ, rfl⟩ := eq_reflection_of_toMatrix f hrm hκρ
  have hmain := etaOK_four_of_dMax hp hG hφ hψ hx hr hne
  rwa [sum_smul_coord_apply_sum f w ρ, sum_smul_coord_apply_sum f κ v] at hmain

theorem mul_eq_two_of_orderOf_eq_four (hp : p ≠ 2) {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod p) U) {x r : U ≃ₗ[ZMod p] U} {v w ρ κ : Fin n → ZMod p}
    (hxm : LinearMap.toMatrix f f x.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2)
    (hrm : LinearMap.toMatrix f f r.toLinearMap = 1 - Matrix.vecMulVec ρ κ)
    (hκρ : ∑ i, κ i * ρ i = 2) (h : orderOf (x * r) = 4) :
    (∑ i, w i * ρ i) * (∑ i, κ i * v i) = 2 := by
  obtain ⟨hφ, rfl⟩ := eq_reflection_of_toMatrix f hxm hwv
  obtain ⟨hψ, rfl⟩ := eq_reflection_of_toMatrix f hrm hκρ
  have h1 := apply_mul_apply_eq_two_of_orderOf_eq_four hp hφ hψ h
  rwa [sum_smul_coord_apply_sum f w ρ, sum_smul_coord_apply_sum f κ v] at h1

theorem eq_zero_of_commute_of_toMatrix (hp : p ≠ 2) {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod p) U) {x r : U ≃ₗ[ZMod p] U} {v w ρ κ : Fin n → ZMod p}
    (hxm : LinearMap.toMatrix f f x.toLinearMap = 1 - Matrix.vecMulVec v w)
    (hwv : ∑ i, w i * v i = 2)
    (hrm : LinearMap.toMatrix f f r.toLinearMap = 1 - Matrix.vecMulVec ρ κ)
    (hκρ : ∑ i, κ i * ρ i = 2) (hc : x * r = r * x) (hne : x ≠ r) :
    ∑ i, w i * ρ i = 0 ∧ ∑ i, κ i * v i = 0 := by
  obtain ⟨hφ, rfl⟩ := eq_reflection_of_toMatrix f hxm hwv
  obtain ⟨hψ, rfl⟩ := eq_reflection_of_toMatrix f hrm hκρ
  have hcomm : Commute (Module.reflection hφ) (Module.reflection hψ) := hc
  refine ⟨?_, ?_⟩
  · have h1 := apply_eq_zero_of_commute hp hφ hψ hcomm hne
    rwa [sum_smul_coord_apply_sum f w ρ] at h1
  · have h2 := apply_eq_zero_of_commute hp hψ hφ hcomm.symm (Ne.symm hne)
    rwa [sum_smul_coord_apply_sum f κ v] at h2

theorem mul_eq_one_or_two_of_etaOK_four {s t : ZMod p} (h : EtaOK 4 s t) (ht : t ≠ 0) :
    s * t = 1 ∨ s * t = 2 := by
  unfold EtaOK at h
  rcases h with h | h | h | h
  · exact absurd h.2 ht
  · exact Or.inl h.2
  · exact Or.inr h.2
  · exact absurd h.1 (by norm_num)

end CFSG.StandardType.ZS.FFourCoord

end
