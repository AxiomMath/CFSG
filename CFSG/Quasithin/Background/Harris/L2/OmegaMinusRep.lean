module

public import CFSG.Quasithin.Background.Harris.L2.OmegaMinusGL
public import CFSG.Quasithin.Background.Harris.L2.OmegaMinusCoord
public import CFSG.Quasithin.SteinbergCBOmegaFourMinus

public section

namespace CFSG.Quasithin.G11.Harris.L2

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.SteinbergCB Matrix
open scoped MatrixGroups

variable {F : Type} [Field F] [Finite F] {a : ℕ} {σ : F →+* F}

theorem twistRep_range_eq (ha : 1 ≤ a) (hF : Nat.card F = (2 ^ a) ^ 2)
    (hσ : ∀ x, σ x = x ^ 2 ^ a) :
    (twistRep (frob_frob hF hσ)).range =
      ⁅isometryGroup (twistedDet σ), isometryGroup (twistedDet σ)⁆ := by
  obtain ⟨-, -, -, ρ, hρ, -, -, Q, hQ, -, -, -, -, hQinv, hinj, hrange, -, -⟩ :=
    SL2_q0sq_Omega4minus_twisted_tensor a ha hF σ hσ
  have hρ' : ρ = twistRep (frob_frob hF hσ) :=
    MonoidHom.ext fun g => LinearEquiv.ext fun X =>
      Subtype.ext ((hρ g X).trans (twistRep_apply _ g X).symm)
  have hQ' : Q = twistedDet σ :=
    QuadraticMap.ext fun X => Subtype.ext ((hQ X).trans (twistedDet_apply X).symm)
  rw [← hρ', ← hQ']
  exact hrange

theorem statedQuadMinus_map {K K' : Type} [Field K] [Field K'] (e : K ≃+* K') (b c : K)
    (v : QIdx → K) :
    StatedQuadMinus 2 K' (e b) (e c) (fun i => e (v i)) = e (StatedQuadMinus 2 K b c v) := by
  simp only [statedQuadMinus_two, map_add, map_mul, map_pow]

theorem glMap_injective {K K' : Type} [Field K] [Field K'] {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : K →+* K') : Function.Injective (Matrix.GeneralLinearGroup.map (n := ι) e) := by
  intro A B h
  ext i j
  have := congrArg (fun C : GL ι K' => (C : Matrix ι ι K') i j) h
  exact e.injective (by simpa using this)

theorem exists_omegaRep (ha : 1 ≤ a) (hF : Nat.card F = (2 ^ a) ^ 2)
    (hσ : ∀ x, σ x = x ^ 2 ^ a) {K' : Type} [Field K'] (e : frobFixed σ ≃+* K') {ω : F}
    (hω : σ ω ≠ ω) :
    ∃ (M : SL(2, F) →* GL QIdx K') (ψ : twistedForm σ ≃+ (QIdx → K')) (b c : K'),
      (∀ s : K', s ^ 2 + b * s + c ≠ 0) ∧ Function.Injective M ∧
      M.range = StatedOmega (StatedQuadMinus 2 K' b c) ∧
      (∀ γ X, ψ (twistRep (frob_frob hF hσ) γ X) = (M γ : Matrix QIdx QIdx K') *ᵥ ψ X) ∧
      (∀ γ v, StatedQuadMinus 2 K' b c ((M γ : Matrix QIdx QIdx K') *ᵥ v) =
        StatedQuadMinus 2 K' b c v) := by
  have h2 := two_eq_zero_of_card ha hF
  have hinv := frob_frob hF hσ
  set τ := twistCoords hinv hω with hτ
  set b₀ := coordB hinv ω
  set c₀ := coordC hinv ω
  let M₀ : SL(2, F) →* GL QIdx (frobFixed σ) :=
    (conjGL τ).toMonoidHom.comp (twistRep hinv)
  let M : SL(2, F) →* GL QIdx K' := (Matrix.GeneralLinearGroup.map (e : frobFixed σ →+* K')).comp M₀
  have hQ₀ : ∀ u, StatedQuadMinus 2 (frobFixed σ) b₀ c₀ (τ u) = twistedDet σ u := fun u => by
    rw [← twistedDet_coordInv hinv ω h2, ← twistCoords_symm_apply hinv hω,
      LinearEquiv.symm_apply_apply]
  have hQ' : ∀ v : QIdx → frobFixed σ,
      StatedQuadMinus 2 K' (e b₀) (e c₀) (fun i => e (v i)) =
        e (StatedQuadMinus 2 (frobFixed σ) b₀ c₀ v) := statedQuadMinus_map e b₀ c₀
  have hM₀ : ∀ γ v, StatedQuadMinus 2 (frobFixed σ) b₀ c₀ ((M₀ γ : Matrix QIdx QIdx _) *ᵥ v) =
      StatedQuadMinus 2 (frobFixed σ) b₀ c₀ v := fun γ =>
    (conjGL_preserves_iff τ (twistedDet σ) _ hQ₀ (twistRep hinv γ)).2
      (twistedDet_twistRep hinv γ)
  refine ⟨M, (τ.toAddEquiv.trans (AddEquiv.piCongrRight fun _ => e.toAddEquiv)), e b₀, e c₀,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro s h
    obtain ⟨t, rfl⟩ := e.surjective s
    apply coordB_nonsplit hinv h2 hω t
    apply e.injective
    simpa using h
  · exact (glMap_injective _).comp ((conjGL τ).injective.comp (twistRep_injective h2 hinv))
  · have h1 : M.range = (M₀.range).map (Matrix.GeneralLinearGroup.map (e : frobFixed σ →+* K')) :=
      MonoidHom.range_comp _ _
    have h3 : M₀.range = StatedOmega (StatedQuadMinus 2 (frobFixed σ) b₀ c₀) := by
      rw [statedOmega_eq_map τ (twistedDet σ) _ hQ₀, ← twistRep_range_eq ha hF hσ]
      exact MonoidHom.range_comp _ _
    rw [h1, h3, statedOmega_map_eq e _ _ hQ']
  · intro γ X
    have := map_mulVec_comp e (M₀ γ) (τ X)
    change (fun i => e (τ (twistRep hinv γ X) i)) =
      ((Matrix.GeneralLinearGroup.map (e : frobFixed σ →+* K') (M₀ γ) : Matrix QIdx QIdx K') *ᵥ
        (fun i => e (τ X i)))
    rw [this]
    funext i
    have h3 := conjGL_mulVec τ (twistRep hinv γ) (τ X)
    rw [LinearEquiv.symm_apply_apply] at h3
    exact congrArg e (congrFun h3.symm i)
  · intro γ v'
    have hv : v' = fun i => e (e.symm (v' i)) := by funext i; simp
    rw [hv]
    change StatedQuadMinus 2 K' (e b₀) (e c₀) ((Matrix.GeneralLinearGroup.map
      (e : frobFixed σ →+* K') (M₀ γ) : Matrix QIdx QIdx K') *ᵥ _) = _
    rw [map_mulVec_comp, hQ', hQ', hM₀]

end CFSG.Quasithin.G11.Harris.L2
