module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2dAuxClass
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2bAux
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2eCase3b

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem
open CFSG.LieType.Universal.Spin

theorem levTwoS2d_cl_outside {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) {Φ : Set (Fin n → ℤ)}
    (hΦ : LevTwoData (isFiniteType_cartanD n) p c Φ) {β γ : Fin n → ℤ}
    (hβ : IsRt (isFiniteType_cartanD n) β) (hγ : IsRt (isFiniteType_cartanD n) γ)
    (hβΦ : β ∉ Φ) (hγΦ : γ ∉ Φ) :
    Cl (isFiniteType_cartanD n) (Φ ∪ {β}) γ := by
  rcases levTwoS2d_classification n hn hp2 c hΦ with
    hzero | ⟨k, c₀, hc₀, hk, hzero⟩ | ⟨c₀, hc₀, hd⟩
  ·
    exfalso
    apply hβΦ
    rw [levTwoS2d_Phi_eq_lambda n hn p hp2 c hΦ]
    refine ⟨hβ, ?_⟩
    rw [levTwoS2d_lam_coord n hn hp2 c β]
    apply Finset.sum_eq_zero
    intro a _
    rw [hzero a, mul_zero]
  ·
    obtain ⟨a, σ, τ, hak, hσ, hτ, hβc⟩ :=
      levTwoS2d_coord_of_notMem n hn hp2 c hΦ hzero hβ hβΦ
    obtain ⟨b, ν, μ, hbk, hν, hμ, hγc⟩ :=
      levTwoS2d_coord_of_notMem n hn hp2 c hΦ hzero hγ hγΦ
    have hβeq : β = levTwoS2d_ofCoord n k a σ τ (Ne.symm hak) hσ hτ :=
      levTwoS2d_eq_ofCoord n hn (Ne.symm hak) hσ hτ hβc
    have hγeq : γ = levTwoS2d_ofCoord n k b ν μ (Ne.symm hbk) hν hμ :=
      levTwoS2d_eq_ofCoord n hn (Ne.symm hbk) hν hμ hγc
    have hxcl : Cl (isFiniteType_cartanD n) (Φ ∪ {β})
        (levTwoS2d_ofCoord n k a σ τ (Ne.symm hak) hσ hτ) := by
      rw [← hβeq]
      exact Cl.base (Or.inr rfl)
    have hreach := levTwoS2d_reach_coord n hn hp2 c hΦ hzero
      (S := Φ ∪ {β}) (by intro x hx; exact Or.inl hx) hak hσ hτ hxcl
    rw [hγeq]
    exact hreach b hbk ν μ hν hμ
  ·
    exact levTwoS2e_cl_outside_case3 n hn hp2 c hΦ hc₀ hd hβ hγ hβΦ hγΦ

theorem levTwoS2d_tcRoot {p : ℕ} [Fact p.Prime] (n : ℕ) (hn : 4 ≤ n) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) {Φ : Set (Fin n → ℤ)}
    (hΦ : LevTwoData (isFiniteType_cartanD n) p c Φ) :
    TCRoot (isFiniteType_cartanD n) Φ := by
  intro S hS
  by_cases hex : ∃ β ∈ S, β ∉ Φ
  · obtain ⟨β, hβS, hβΦ⟩ := hex
    refine ⟨{β}, ?_, ?_, ?_⟩
    · intro x hx
      have hxβ : x = β := by simpa using hx
      rw [hxβ]; exact hβS
    · simp
    · refine levTwoS2b_cl_eq_of_subset (isFiniteType_cartanD n) ?_ ?_
      · intro x hx
        have hxβ : x = β := by simpa using hx
        rw [hxβ]; exact hβS
      · intro γ hγS
        by_cases hγΦ : γ ∈ Φ
        · exact Cl.base (Or.inl hγΦ)
        · have hset : (Φ ∪ (↑({β} : Finset (Fin n → ℤ)) : Set (Fin n → ℤ))) = Φ ∪ {β} := by
            rw [Finset.coe_singleton]
          rw [hset]
          exact levTwoS2d_cl_outside n hn hp2 c hΦ (hS β hβS) (hS γ hγS) hβΦ hγΦ
  · have hex' : ∀ γ, γ ∈ S → γ ∈ Φ := by
      intro γ hγS
      by_contra hc
      exact hex ⟨γ, hγS, hc⟩
    refine ⟨∅, ?_, ?_, ?_⟩
    · intro x hx; exact absurd hx (by simp)
    · simp
    · refine levTwoS2b_cl_eq_of_subset (isFiniteType_cartanD n) ?_ ?_
      · intro x hx; exact absurd hx (by simp)
      · intro γ hγS
        exact Cl.base (Or.inl (hex' γ hγS))


theorem levTwoS2d_engine_of_eq {n : ℕ} {R R' : Matrix (Fin n) (Fin n) ℤ} (h : R = R')
    (hR : TauCeti.IsFiniteType R) (hR' : TauCeti.IsFiniteType R')
    (H : ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (c : Fin n → ZMod p) (Φ : Set (Fin n → ℤ)),
      LevTwoData hR p c Φ → TCRoot hR Φ) :
    ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (c : Fin n → ZMod p) (Φ : Set (Fin n → ℤ)),
      LevTwoData hR' p c Φ → TCRoot hR' Φ := by
  subst h
  exact H

end CFSG.StandardType.LevTwo

