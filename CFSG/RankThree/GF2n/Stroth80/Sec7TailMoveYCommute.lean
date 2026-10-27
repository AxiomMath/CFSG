module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveFrame

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG.CGT.Timmesfeld75
open scoped commutatorElement

variable {K E X : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E] [Group X]
  [Finite X] {B : LinearMap.BilinForm K E} {φ : X →* (E ≃ₗ[K] E)} {V L Nb Rb : Subgroup X}
  {Tt : X → Submodule K E} {q : ℕ}

theorem MoveFrame.Y_commute_Yx (F : MoveFrame B φ V L Nb Rb Tt q) (h : X)
    (hK : ∀ a ∈ V, h * a * h⁻¹ ∈ normalizer (V : Set X))
    (hN : ¬ ∀ a ∈ V, h * a * h⁻¹ ∈ Nb)
    (hcomm : ∀ v ∈ V, ∀ a ∈ V, v * (h * a * h⁻¹) = (h * a * h⁻¹) * v)
    (hRb : ∀ a ∈ V, h * a * h⁻¹ ∈ Rb)
    (hVnot : ∀ a ∈ V, a ≠ 1 → ∀ n ∈ L, (h * a * h⁻¹) * n * (h * a * h⁻¹)⁻¹ * n⁻¹ ∈ V →
      (h * a * h⁻¹) * n * (h * a * h⁻¹)⁻¹ * n⁻¹ = 1) :
    ∀ x ∈ L, ∀ a ∈ V, ∀ b ∈ V,
      (h * a * h⁻¹) * (x * (h * b * h⁻¹) * x⁻¹) =
        (x * (h * b * h⁻¹) * x⁻¹) * (h * a * h⁻¹) := by
  intro x hx a ha b hb
  by_cases ha1 : a = 1
  · subst ha1
    simp
  have hyb : h * b * h⁻¹ ∈ normalizer (V : Set X) := hK b hb
  have hc12 : Commute (h * a * h⁻¹) (h * b * h⁻¹) := by
    have hab : a * b = b * a := F.V_comm a ha b hb
    show (h * a * h⁻¹) * (h * b * h⁻¹) = (h * b * h⁻¹) * (h * a * h⁻¹)
    calc (h * a * h⁻¹) * (h * b * h⁻¹) = h * (a * b) * h⁻¹ := by group
      _ = h * (b * a) * h⁻¹ := by rw [hab]
      _ = (h * b * h⁻¹) * (h * a * h⁻¹) := by group
  obtain ⟨d, hd_def⟩ : ∃ d : X, d = x * (h * b * h⁻¹) * x⁻¹ * (h * b * h⁻¹)⁻¹ :=
    ⟨_, rfl⟩
  have hL1 : (h * b * h⁻¹) * x * (h * b * h⁻¹)⁻¹ ∈ L := F.L_norm (h * b * h⁻¹) hyb x hx
  have hd : d ∈ L := by
    have e : d = x * ((h * b * h⁻¹) * x * (h * b * h⁻¹)⁻¹)⁻¹ := by
      rw [hd_def]
      group
    rw [e]
    exact mul_mem hx (inv_mem hL1)
  have hT : ⁅h * a * h⁻¹, ⁅x, h * b * h⁻¹⁆⁆ ∈ V := F.transvection h hRb hN a ha b hb x hx
  have hcd : ⁅x, h * b * h⁻¹⁆ = d := by
    rw [commutatorElement_def, hd_def]
  rw [hcd, commutatorElement_def] at hT
  have hT1 : (h * a * h⁻¹) * d * (h * a * h⁻¹)⁻¹ * d⁻¹ = 1 := hVnot a ha ha1 d hd hT
  have hyd : Commute (h * a * h⁻¹) d := by
    show (h * a * h⁻¹) * d = d * (h * a * h⁻¹)
    have e : (h * a * h⁻¹) * d * (d * (h * a * h⁻¹))⁻¹ =
        (h * a * h⁻¹) * d * (h * a * h⁻¹)⁻¹ * d⁻¹ := by
      group
    exact mul_inv_eq_one.mp (e.trans hT1)
  have hp : x * (h * b * h⁻¹) * x⁻¹ = d * (h * b * h⁻¹) := by
    rw [hd_def]
    group
  rw [hp]
  exact hyd.mul_right hc12

end CFSG.RankThree.GF2n.Stroth80
