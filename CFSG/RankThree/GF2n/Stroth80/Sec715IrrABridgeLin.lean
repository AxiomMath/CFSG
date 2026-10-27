module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open Module

variable {K X H : Type*} [Field K] [AddCommGroup X] [Module K X] [Group H]

theorem exists_ne_one_of_irr [FiniteDimensional K X] (ρ : H →* (X ≃ₗ[K] X))
    (hirr : ∀ S : Submodule K X, (∀ h : H, ∀ x ∈ S, ρ h x ∈ S) → S = ⊥ ∨ S = ⊤)
    (hX : 1 < finrank K X) : ∃ h : H, ρ h ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hpos : 0 < finrank K X := lt_trans Nat.zero_lt_one hX
  haveI : Nontrivial X := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  have hinv : ∀ h : H, ∀ y ∈ K ∙ x, ρ h y ∈ K ∙ x := fun h y hy => by
    rw [hcon h]
    exact hy
  rcases hirr _ hinv with h | h
  · exact hx ((Submodule.span_singleton_eq_bot).mp h)
  · have h1 : finrank K ↥(K ∙ x) = 1 := finrank_span_singleton hx
    rw [h, finrank_top] at h1
    omega

theorem quadraticForm_ne_zero_of_nd [Nontrivial X] (q : QuadraticForm K X)
    (hnd : ∀ a : X, (∀ a' : X, QuadraticMap.polar q a a' = 0) → a = 0) : q ≠ 0 := by
  intro hq
  obtain ⟨x, hx⟩ := exists_ne (0 : X)
  refine hx (hnd x fun a' => ?_)
  rw [hq]
  simp [QuadraticMap.polar]

theorem eq_one_of_coord {L : Type*} [AddCommGroup L] [Module K L] (a : H →* (X ≃ₗ[K] X))
    (ρ : H →* (L ≃ₗ[K] L)) (e : X ≃ₗ[K] (Fin 2 → L))
    (he : ∀ h x, e (a h x) = fun i => ρ h (e x i)) {h : H} (hh : a h = 1) : ρ h = 1 := by
  classical
  refine LinearEquiv.ext fun c => ?_
  have h1 := congrFun (he h (e.symm (Pi.single 0 c))) 0
  rw [hh, LinearEquiv.apply_symm_apply] at h1
  simp only [Pi.single_eq_same] at h1
  rw [LinearEquiv.coe_one, id]
  exact h1.symm.trans (by rw [show (1 : X ≃ₗ[K] X) (e.symm (Pi.single 0 c)) =
    e.symm (Pi.single 0 c) from rfl, LinearEquiv.apply_symm_apply, Pi.single_eq_same])

end CFSG.RankThree.GF2n.Stroth80.S715L
