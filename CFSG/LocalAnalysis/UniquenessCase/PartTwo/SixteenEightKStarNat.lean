module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKMap

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W W' : Type} [CommGroup W] [CommGroup W'] {H : Subgroup (MulAut W)}
  {H' : Subgroup (MulAut W')} {I Z : Subgroup W}

theorem s16k_realizes_map_bot {D : FFModel} (hR : D.Realizes H I Z) (ρ : W →* W')
    (hker : ρ.ker = Z) (θ : ↥H →* ↥H') (hθ : Function.Surjective θ)
    (hequiv : ∀ (h : ↥H) (w : W), ρ ((h : MulAut W) w) = ((θ h : ↥H') : MulAut W') (ρ w)) :
    D.Realizes H' (I.map ρ) ⊥ := by
  have h1 := s16k_realizes_map hR ρ hker.le θ hθ hequiv
  rwa [(Subgroup.map_eq_bot_iff _).2 hker.ge] at h1

theorem s16k_binaryNaturalSL_map {n a : ℕ} (hN : BinaryNaturalSL H I Z n a) (ρ : W →* W')
    (hker : ρ.ker = Z) (θ : ↥H →* ↥H') (hθ : Function.Surjective θ)
    (hequiv : ∀ (h : ↥H) (w : W), ρ ((h : MulAut W) w) = ((θ h : ↥H') : MulAut W') (ρ w)) :
    BinaryNaturalSL H' (I.map ρ) ⊥ n a := by
  obtain ⟨K, hF, hFin, hK, hR⟩ := hN
  exact ⟨K, hF, hFin, hK, s16k_realizes_map_bot hR ρ hker θ hθ hequiv⟩

theorem s16k_natSpn_map {n a : ℕ} (hN : NatSpn H I Z n a) (ρ : W →* W') (hker : ρ.ker = Z)
    (θ : ↥H →* ↥H') (hθ : Function.Surjective θ)
    (hequiv : ∀ (h : ↥H) (w : W), ρ ((h : MulAut W) w) = ((θ h : ↥H') : MulAut W') (ρ w)) :
    NatSpn H' (I.map ρ) ⊥ n a := by
  obtain ⟨he, K, hF, hFin, hK, hR⟩ := hN
  exact ⟨he, K, hF, hFin, hK, s16k_realizes_map_bot hR ρ hker θ hθ hequiv⟩

theorem s16k_natOmegaPlus_map {n a : ℕ} (hN : NatOmegaPlus H I Z n a) (ρ : W →* W')
    (hker : ρ.ker = Z) (θ : ↥H →* ↥H') (hθ : Function.Surjective θ)
    (hequiv : ∀ (h : ↥H) (w : W), ρ ((h : MulAut W) w) = ((θ h : ↥H') : MulAut W') (ρ w)) :
    NatOmegaPlus H' (I.map ρ) ⊥ n a := by
  obtain ⟨he, K, hF, hFin, hK, hR⟩ := hN
  exact ⟨he, K, hF, hFin, hK, s16k_realizes_map_bot hR ρ hker θ hθ hequiv⟩

theorem s16k_natOmegaMinus_map {n a : ℕ} (hN : NatOmegaMinus H I Z n a) (ρ : W →* W')
    (hker : ρ.ker = Z) (θ : ↥H →* ↥H') (hθ : Function.Surjective θ)
    (hequiv : ∀ (h : ↥H) (w : W), ρ ((h : MulAut W) w) = ((θ h : ↥H') : MulAut W') (ρ w)) :
    NatOmegaMinus H' (I.map ρ) ⊥ n a := by
  obtain ⟨he, K, hF, hFin, b, c, hK, hirr, hR⟩ := hN
  exact ⟨he, K, hF, hFin, b, c, hK, hirr, s16k_realizes_map_bot hR ρ hker θ hθ hequiv⟩

theorem s16k_alternatingNatural_map {n : ℕ} (hN : AlternatingNatural H I Z n) (ρ : W →* W')
    (hker : ρ.ker = Z) (θ : ↥H →* ↥H') (hθ : Function.Surjective θ)
    (hequiv : ∀ (h : ↥H) (w : W), ρ ((h : MulAut W) w) = ((θ h : ↥H') : MulAut W') (ρ w)) :
    AlternatingNatural H' (I.map ρ) ⊥ n :=
  s16k_realizes_map_bot hN ρ hker θ hθ hequiv

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
