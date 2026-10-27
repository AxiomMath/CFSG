module

public import CFSG.LocalAnalysis.StandardType.FS81.N7MainAlg

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

structure N7MSetup (X : Type) [Group X] [Finite X] where
  ρ : X →* Matrix (Fin 8) (Fin 8) (ZMod 3)
  ρ_inj : Function.Injective ρ
  surj_H1 : ∀ A ∈ evenAll0 7, ∃ x, ρ x = A
  norm_iff : ∀ x : X, (∃ c : ZMod 3, ρ x *ᵥ nmE0 = c • nmE0) ↔ ρ x ∈ evenAll0 7
  odd_core : ∀ N : Subgroup X, N.Normal → Odd (Nat.card N) → N = ⊥
  big : 2 ^ 8 * Nat.factorial 8 < Nat.card X

namespace N7MSetup

variable {X : Type} [Group X] [Finite X] (S : N7MSetup X)

@[expose] def FKgrp : Subgroup X where
  carrier := {x | S.ρ x ∈ nmFK}
  mul_mem' := by
    intro x y hx hy
    show S.ρ (x * y) ∈ nmFK
    rw [map_mul]
    exact nmFK_mul hx hy
  one_mem' := by
    show S.ρ 1 ∈ nmFK
    rw [map_one]
    exact nmFK_one
  inv_mem' := by
    intro x hx
    show S.ρ x⁻¹ ∈ nmFK
    exact nmFK_of_mul_eq_one hx (by rw [← map_mul, mul_inv_cancel, map_one])

@[expose] def Fgrp : Subgroup X where
  carrier := {x | S.ρ x ∈ nmF}
  mul_mem' := by
    intro x y hx hy
    show S.ρ (x * y) ∈ nmF
    rw [map_mul]
    exact nmF_mul hx hy
  one_mem' := by
    show S.ρ 1 ∈ nmF
    rw [map_one]
    exact nmF_one
  inv_mem' := by
    intro x hx
    show S.ρ x⁻¹ ∈ nmF
    have h1 : S.ρ x * S.ρ x⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have h2 : S.ρ x * S.ρ x = 1 := nmF_sq hx
    have h3 : S.ρ x⁻¹ = S.ρ x := by
      calc S.ρ x⁻¹ = (S.ρ x * S.ρ x) * S.ρ x⁻¹ := by rw [h2, one_mul]
        _ = S.ρ x * (S.ρ x * S.ρ x⁻¹) := by rw [mul_assoc]
        _ = S.ρ x := by rw [h1, mul_one]
    rw [h3]
    exact hx

theorem mem_FKgrp (x : X) : x ∈ S.FKgrp ↔ S.ρ x ∈ nmFK := Iff.rfl

theorem mem_Fgrp (x : X) : x ∈ S.Fgrp ↔ S.ρ x ∈ nmF := Iff.rfl

theorem fix_iff (x : X) : S.ρ x *ᵥ nmE0 = nmE0 ↔ S.ρ x ∈ evenFix0 7 := by
  constructor
  · intro h
    have hmem : S.ρ x ∈ evenAll0 7 := (S.norm_iff x).mp ⟨1, by rw [h, one_smul]⟩
    obtain ⟨σ, s, hs, ⟨hσ0, hps⟩, hA⟩ := hmem
    have h2 : (spMat σ s *ᵥ nmE0) (σ 0) = s 0 * nmE0 0 := by
      rw [spMat_mulVec]
      simp [Equiv.symm_apply_apply]
    have hs0 : s 0 = 1 := by
      have hcoord := congrFun h (σ 0)
      rw [hA, h2, hσ0] at hcoord
      simpa [nmE0] using hcoord
    have hps7 : ∏ i : Fin 7, s i.succ = 1 := by
      have hsucc := Fin.prod_univ_succ (f := s)
      rw [hsucc, hs0, one_mul] at hps
      exact hps
    exact ⟨σ, s, hs, ⟨hσ0, hs0, hps7⟩, hA⟩
  · rintro ⟨σ, s, hs, ⟨hσ0, hs0, hps⟩, hA⟩
    rw [hA]
    funext i
    rw [spMat_mulVec]
    show s (σ.symm i) * nmE0 (σ.symm i) = nmE0 i
    by_cases hi : i = 0
    · subst hi
      have hsymm : σ.symm 0 = 0 := by simpa [hσ0] using Equiv.symm_apply_apply σ 0
      rw [hsymm, hs0]
      simp [nmE0]
    · have hsymm : σ.symm i ≠ 0 :=
        fun h => hi (by rw [← Equiv.apply_symm_apply σ i, h, hσ0])
      simp [nmE0, hsymm, Ne.symm hsymm, hi, Ne.symm hi]

end N7MSetup

end CFSG.StandardType.FrameRoute.FS81

end
