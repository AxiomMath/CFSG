module

public import CFSG.RankThree.GF2n.Smith81.S81RD8Stab
public import CFSG.RankThree.GF2n.Smith81.S81RD8Kill
public import CFSG.RankThree.GF2n.Smith81.S81RD8Span

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open Matrix exteriorPower

variable {K : Type} [Field K]

theorem pure_range_support {x : GL (Fin 6) K} {a f : Fin 6 → K}
    (hx : (x : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec a f) (hfa : f ⬝ᵥ a = 0) (ha : a ≠ 0)
    (hf : f ≠ 0) {s : Fin 3 → Fin 6 → K} (hs : LinearIndependent K s)
    (hmem : ιMulti K 3 s ∈ LinearMap.range (rho K x - 1)) :
    (∀ i, f ⬝ᵥ s i = 0) ∧ a ∈ Submodule.span K (Set.range s) := by
  obtain ⟨η, hη⟩ := LinearMap.mem_range.mp hmem
  have hfixc : ∀ (σ : GL (Fin 6) K) (θ : Fin 6 → K),
      (σ : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec a θ → θ ⬝ᵥ a = 0 →
        rho K σ (ιMulti K 3 s) = ιMulti K 3 s := by
    intro σ θ hσ hθa
    have h1 : (rho K σ - 1) (ιMulti K 3 s) = 0 := by
      rw [← hη]
      exact LinearMap.congr_fun (rho_kill_centre hσ hx hθa) η
    rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h1
  have hfixa : ∀ (σ : GL (Fin 6) K) (w : Fin 6 → K),
      (σ : Matrix (Fin 6) (Fin 6) K) = 1 + vecMulVec w f → rho K σ (ιMulti K 3 s) = ιMulti K 3 s := by
    intro σ w hσ
    have h1 : (rho K σ - 1) (ιMulti K 3 s) = 0 := by
      rw [← hη]
      exact LinearMap.congr_fun (rho_kill_axis hσ hx hfa) η
    rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h1
  refine ⟨?_, ?_⟩
  ·
    by_contra hnot
    obtain ⟨w, hfw, hw⟩ := exists_dot_ker_not_mem_span hf s
    obtain ⟨σ, hσ⟩ := exists_gl_one_add_vecMulVec w f hfw
    rcases stab_pure hσ hs (hfixa σ w hσ) with h | h
    · exact hnot h
    · exact hw h
  ·
    by_contra hnot
    have hall : ∀ θ : Fin 6 → K, θ ⬝ᵥ a = 0 → ∀ i, θ ⬝ᵥ s i = 0 := by
      intro θ hθ
      obtain ⟨σ, hσ⟩ := exists_gl_one_add_vecMulVec a θ hθ
      rcases stab_pure hσ hs (hfixc σ θ hσ hθ) with h | h
      · exact h
      · exact absurd h hnot
    have hcol : ∀ i, ∃ c : K, s i = c • a := by
      intro i
      by_contra hno
      have hno' : ∀ c : K, s i ≠ c • a := fun c hc => hno ⟨c, hc⟩
      obtain ⟨θ, hθa, hθs⟩ := exists_dot_eq_zero_dot_ne ha hno'
      exact hθs (hall θ hθa i)
    exact not_linearIndependent_of_collinear hcol hs

end CFSG.RankThree.GF2n.Smith81.A5Cube
