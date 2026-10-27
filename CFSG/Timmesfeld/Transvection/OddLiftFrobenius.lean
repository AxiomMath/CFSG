module

public import CFSG.Timmesfeld.Transvection.OddPairs
public import CFSG.Timmesfeld.Transvection.OddModelHeis
public import CFSG.Timmesfeld.Transvection.OddSU3Chord
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2OverlapValField
import CFSG.Timmesfeld.Transvection.OddSU3Aut

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.Timmesfeld.Transvection.Pres
  CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.SeitzReduction.F4Pilot (suCongr coe_suCongr)
open scoped commutatorElement

section Congr

variable {F : Type*} [Field F] {σ : F ≃+* F}

theorem suCongr_suHeis (hσ : ∀ c, σ (σ c) = c) {m : ℕ} (hm : ¬Even m) (τ : F ≃+* F)
    (hτ : ∀ c, τ (σ c) = σ (τ c)) (a : Fin (m / 2) ⊕ Fin (m / 2)) (u v : F) :
    suCongr τ hτ m (suHeis σ hσ hm a u v) = suHeis σ hσ hm a (τ u) (τ v) := by
  by_cases h : v + σ v + σ u * u = 0
  · have h' : τ v + σ (τ v) + σ (τ u) * τ u = 0 := by
      rw [← hτ, ← hτ, ← map_mul, ← map_add, ← map_add, h, map_zero]
    apply mat_injective
    rw [mat_apply, coe_suCongr, ← mat_apply, mat_suHeis hσ hm h, mat_suHeis hσ hm h']
    rw [heisenbergMatrix, heisenbergMatrix, Matrix.map_add _ (map_add τ),
      Matrix.map_sub _ (map_sub τ), Matrix.map_add _ (map_add τ),
      Matrix.map_one _ (map_zero τ) (map_one τ), Matrix.map_single, Matrix.map_single,
      Matrix.map_single, hτ]
  · have h' : ¬ (τ v + σ (τ v) + σ (τ u) * τ u = 0) := by
      intro hc
      apply h
      have hc' : τ (v + σ v + σ u * u) = 0 := by
        rw [map_add, map_add, map_mul, hτ, hτ]
        exact hc
      exact τ.injective (by simpa using hc')
    rw [suHeis_of_not hσ hm h, suHeis_of_not hσ hm h', map_one]

end Congr

section Chord

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem suCongr_comp_su3Chord (hFn : Nat.card F = (2 ^ n) ^ 2) (τ : F ≃+* F)
    (hτ : ∀ c, τ (unitaryInvolution F 2 n c) = unitaryInvolution F 2 n (τ c))
    (hfix : ∀ c, unitaryInvolution F 2 n c = c → τ c = c) :
    (suCongr τ hτ 3).toMonoidHom.comp (su3Chord (unitaryInvolution F 2 n)) =
      su3Chord (unitaryInvolution F 2 n) := by
  let σ := unitaryInvolution F 2 n
  have hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hFn
  have hβ : ∀ (a : Fin (3 / 2) ⊕ Fin (3 / 2)) (c : F),
      suCongr τ hτ 3 (suLong σ a c) = suLong σ a (τ c) := by
    intro a c
    rw [← suHeis_zero_left (σ := σ) hσ (Nat.not_even_two_mul_add_one 1 : ¬ Even 3) a c,
      suCongr_suHeis hσ (Nat.not_even_two_mul_add_one 1 : ¬ Even 3) τ hτ a 0 c, map_zero,
      suHeis_zero_left (σ := σ) hσ (Nat.not_even_two_mul_add_one 1 : ¬ Even 3) a (τ c)]
  have h := su3Chord_comp_of_aligned hFn (α := 1) (β := suCongr τ hτ 3) (ε := 1) (τ := τ)
    (fun c hc => by simp only [MulAut.one_apply, inv_one, one_mul, hfix c hc])
    (fun c hc => by simp only [MulAut.one_apply, inv_one, one_mul, hfix c hc])
    (fun c _ => by rw [one_mul]; exact hβ (Sum.inl (0 : Fin (3 / 2))) c)
    (fun c _ => by rw [inv_one, one_mul]; exact hβ (Sum.inr (0 : Fin (3 / 2))) c)
  rw [show ((1 : MulAut (SU σ 2)).toMonoidHom) = MonoidHom.id _ from rfl,
    MonoidHom.comp_id] at h
  exact h

end Chord

section Lift

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} (hFn : Nat.card F = (2 ^ n) ^ 2)
  {r : ℕ} (hr : 2 ≤ r) {H : Type} [Group H]
  (Ψ₀ : SU (unitaryInvolution F 2 n) (2 * r) →* H)
  (θ : SU (unitaryInvolution F 2 n) 3 →* H)

local notation "heis₃" => suHeis (unitaryInvolution F 2 n) (unitaryInvolution_involutive hFn)
  (Nat.not_even_two_mul_add_one 1 : ¬ Even 3) (Sum.inl (0 : Fin (3 / 2)))

theorem oddPrevLift_comp (e : SU (unitaryInvolution F 2 n) 3 →* SU (unitaryInvolution F 2 n) 3) :
    oddPrevLift hFn hr Ψ₀ (θ.comp e) = (oddPrevLift hFn hr Ψ₀ θ).comp e := rfl

variable {hFn hr Ψ₀ θ}

theorem commutatorElement_suHeis_oddPrevLift_comp
    {e : SU (unitaryInvolution F 2 n) 3 →* SU (unitaryInvolution F 2 n) 3}
    (he : ∀ u v : F, e (heis₃ u v) =
      heis₃ (unitaryInvolution F 2 n u) (unitaryInvolution F 2 n v))
    {ξ : F → H}
    (hheis : ∀ u v u' v' : F,
      v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 →
      v' + unitaryInvolution F 2 n v' + unitaryInvolution F 2 n u' * u' = 0 →
        ⁅θ (heis₃ u v), oddPrevLift hFn hr Ψ₀ θ (heis₃ u' v')⁆ =
          ξ (u * unitaryInvolution F 2 n u'))
    (u v u' v' : F)
    (h : v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0)
    (h' : v' + unitaryInvolution F 2 n v' + unitaryInvolution F 2 n u' * u' = 0) :
    ⁅(θ.comp e) (heis₃ u v), oddPrevLift hFn hr Ψ₀ (θ.comp e) (heis₃ u' v')⁆ =
      ξ (unitaryInvolution F 2 n u * u') := by
  have h1 : unitaryInvolution F 2 n v + unitaryInvolution F 2 n (unitaryInvolution F 2 n v) +
      unitaryInvolution F 2 n (unitaryInvolution F 2 n u) * unitaryInvolution F 2 n u = 0 := by
    rw [← map_mul, ← map_add, ← map_add, h, map_zero]
  have h2 : unitaryInvolution F 2 n v' + unitaryInvolution F 2 n (unitaryInvolution F 2 n v') +
      unitaryInvolution F 2 n (unitaryInvolution F 2 n u') * unitaryInvolution F 2 n u' = 0 := by
    rw [← map_mul, ← map_add, ← map_add, h', map_zero]
  rw [oddPrevLift_comp, MonoidHom.comp_apply, MonoidHom.comp_apply, he, he,
    hheis (unitaryInvolution F 2 n u) (unitaryInvolution F 2 n v)
      (unitaryInvolution F 2 n u') (unitaryInvolution F 2 n v') h1 h2,
    unitaryInvolution_involutive hFn]

theorem commutatorElement_short_suHeis_comp
    {e : SU (unitaryInvolution F 2 n) 3 →* SU (unitaryInvolution F 2 n) 3}
    (he : ∀ u v : F, e (heis₃ u v) =
      heis₃ (unitaryInvolution F 2 n u) (unitaryInvolution F 2 n v))
    {ξ₁ ξ₂ : F → H}
    (hshort : ∀ s u v : F,
      v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0 →
        ⁅ξ₁ s, θ (heis₃ u v)⁆ =
          oddPrevLift hFn hr Ψ₀ θ
              (heis₃ (unitaryInvolution F 2 n s * u) (unitaryInvolution F 2 n s * s * v)) *
            ξ₂ (s * v))
    (s u v : F) (h : v + unitaryInvolution F 2 n v + unitaryInvolution F 2 n u * u = 0) :
    ⁅ξ₁ s, (θ.comp e) (heis₃ u v)⁆ =
      oddPrevLift hFn hr Ψ₀ (θ.comp e) (heis₃ (s * u) (unitaryInvolution F 2 n s * s * v)) *
        ξ₂ (s * unitaryInvolution F 2 n v) := by
  have h1 : unitaryInvolution F 2 n v + unitaryInvolution F 2 n (unitaryInvolution F 2 n v) +
      unitaryInvolution F 2 n (unitaryInvolution F 2 n u) * unitaryInvolution F 2 n u = 0 := by
    rw [← map_mul, ← map_add, ← map_add, h, map_zero]
  rw [oddPrevLift_comp, MonoidHom.comp_apply, MonoidHom.comp_apply, he, he,
    hshort s (unitaryInvolution F 2 n u) (unitaryInvolution F 2 n v) h1]
  have hpar : unitaryInvolution F 2 n (unitaryInvolution F 2 n s * s * v) =
      unitaryInvolution F 2 n s * s * unitaryInvolution F 2 n v := by
    rw [map_mul, map_mul, unitaryInvolution_involutive hFn]
    ring
  rw [show unitaryInvolution F 2 n (s * u) =
      unitaryInvolution F 2 n s * unitaryInvolution F 2 n u from map_mul _ s u, hpar]

end Lift

end CFSG.Timmesfeld.Transvection
