module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveFrameAPI
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveRank

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG.CGT.Timmesfeld75
open scoped commutatorElement

variable {K E X : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
  [Group X] [Finite X]
  {B : LinearMap.BilinForm K E} {φ : X →* (E ≃ₗ[K] E)} {V L Nb Rb : Subgroup X}
  {Tt : X → Submodule K E} {q : ℕ}

theorem MoveFrame.Y_not_conj_into_V (F : MoveFrame B φ V L Nb Rb Tt q) (h : X)
    (hN : ¬ ∀ a ∈ V, h * a * h⁻¹ ∈ Nb)
    (hcomm : ∀ v ∈ V, ∀ a ∈ V, v * (h * a * h⁻¹) = (h * a * h⁻¹) * v)
    (hRb : ∀ a ∈ V, h * a * h⁻¹ ∈ Rb)
    (hVY : ∀ a ∈ V, a ≠ 1 → h * a * h⁻¹ ∉ V) :
    ∀ a ∈ V, a ≠ 1 → ∀ v ∈ V, v ≠ 1 → ∀ (g : X), ∀ w ∈ V,
      g * w * g⁻¹ ≠ (h * a * h⁻¹) * v := by
  intro a ha ha1 v hv hv1 g w hw hgw
  by_cases hw1 : w = 1
  · subst hw1
    have h1 : h * a * h⁻¹ * v = 1 := by
      rw [← hgw]
      simp
    have h2 : h * a * h⁻¹ = v⁻¹ := eq_inv_of_mul_eq_one_left h1
    apply hVY a ha ha1
    rw [h2]
    exact V.inv_mem hv
  · have hr6 := F.finrank_range_opm_conj g hw hw1
    have hab : φ (h * a * h⁻¹) * φ v = φ v * φ (h * a * h⁻¹) := by
      rw [← map_mul, ← map_mul, (hcomm v hv a ha).symm]
    have ha2 : ∀ x, opm (φ (h * a * h⁻¹)) (opm (φ (h * a * h⁻¹)) x) = 0 :=
      fun x => F.opm_sq ha h x
    have hb2 : ∀ x, opm (φ v) (opm (φ v) x) = 0 := by
      intro x
      have hx := F.opm_sq hv 1 x
      rwa [one_mul, inv_one, mul_one] at hx
    have hna : Module.finrank K (LinearMap.range (opm (φ (h * a * h⁻¹)))) = 6 := by
      rw [F.Tt_range h a ha ha1, F.Tt_rank h]
    have hnb : Module.finrank K (LinearMap.range (opm (φ v))) = 6 := by
      rw [F.range_opm_V hv hv1, F.Tt_rank 1]
    have c1 : ∀ a' ∈ V, ∀ b ∈ V,
        (1 * a' * 1⁻¹) * (h * b * h⁻¹) = (h * b * h⁻¹) * (1 * a' * 1⁻¹) := by
      intro a' ha' b hb
      simp only [one_mul, inv_one, mul_one]
      exact hcomm a' ha' b hb
    have c2 : ∀ b ∈ V, 1⁻¹ * (h * b * h⁻¹) * 1 ∈ Rb := by
      intro b hb
      simp only [inv_one, one_mul, mul_one]
      exact hRb b hb
    have c3 : ¬ ∀ b ∈ V, 1⁻¹ * (h * b * h⁻¹) * 1 ∈ Nb := by
      simp only [inv_one, one_mul, mul_one]
      exact hN
    have hi : Module.finrank K ↥(LinearMap.range (opm (φ (h * a * h⁻¹))) ⊓
        LinearMap.range (opm (φ v))) = 2 := by
      rw [F.Tt_range h a ha ha1, F.range_opm_V hv hv1, inf_comm]
      exact F.pair_dim 1 h c1 c2 c3
    have hkey := finrank_range_opm_mul_ge B F.nondeg F.refl F.char2 (φ (h * a * h⁻¹)) (φ v)
      (F.isom (h * a * h⁻¹)) (F.isom v) hab ha2 hb2 6 2 hna hnb hi
    have hprod : φ (h * a * h⁻¹) * φ v = φ (g * w * g⁻¹) := by
      rw [← map_mul, hgw]
    have hr : Module.finrank K (LinearMap.range (opm (φ (h * a * h⁻¹) * φ v))) = 6 := by
      rw [hprod]
      exact hr6
    omega

theorem MoveFrame.Y_hVnot (F : MoveFrame B φ V L Nb Rb Tt q) (h : X)
    (hnc : ∀ a ∈ V, a ≠ 1 → ∀ v ∈ V, v ≠ 1 → ∀ (g : X), ∀ w ∈ V,
      g * w * g⁻¹ ≠ (h * a * h⁻¹) * v) :
    ∀ a ∈ V, a ≠ 1 → ∀ n ∈ L, (h * a * h⁻¹) * n * (h * a * h⁻¹)⁻¹ * n⁻¹ ∈ V →
      (h * a * h⁻¹) * n * (h * a * h⁻¹)⁻¹ * n⁻¹ = 1 := by
  intro a ha ha1 n _hn hc
  by_contra hc1
  have hyy : (h * a * h⁻¹) * (h * a * h⁻¹) = 1 := by
    have e : (h * a * h⁻¹) * (h * a * h⁻¹) = h * (a * a) * h⁻¹ := by group
    rw [e, F.V_sq a ha, mul_one, mul_inv_cancel]
  have hyinv : (h * a * h⁻¹)⁻¹ = h * a * h⁻¹ := (eq_inv_of_mul_eq_one_left hyy).symm
  have hkey : (h * a * h⁻¹) * ((h * a * h⁻¹) * n * (h * a * h⁻¹)⁻¹ * n⁻¹) =
      n * (h * a * h⁻¹) * n⁻¹ := by
    have e : (h * a * h⁻¹) * ((h * a * h⁻¹) * n * (h * a * h⁻¹)⁻¹ * n⁻¹) =
        (h * a * h⁻¹) * (h * a * h⁻¹) * n * (h * a * h⁻¹)⁻¹ * n⁻¹ := by
      group
    rw [e, hyy, one_mul, hyinv]
  have heq : (n * h) * a * (n * h)⁻¹ =
      (h * a * h⁻¹) * ((h * a * h⁻¹) * n * (h * a * h⁻¹)⁻¹ * n⁻¹) := by
    rw [hkey]
    group
  exact hnc a ha ha1 _ hc hc1 (n * h) a ha heq

end CFSG.RankThree.GF2n.Stroth80

end
