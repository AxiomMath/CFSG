module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylNormDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylGenModel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylGenLift

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB Multiplicative

section Transfer

variable {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}

theorem ggAutomizer_eq_map_ggTorusInduced {k : ℕ} {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* R} (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    {A : Subgroup (MulAut L')} {τ : Multiplicative (Fin k → ZMod p) →* R}
    {σ : Multiplicative (Fin k → ZMod p) →* L'} (Θ : Multiplicative (Fin k → ZMod p) ≃* ↥A)
    (hψσ : ∀ f, ψ (σ f) = τ f) (hΘ : ∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f))
    (hnorm : ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      ∃ u ∈ ggTorusInduced τ, ∀ f, ψ n * τ f * (ψ n)⁻¹ = τ (u f)) :
    ggAutomizer (MulAut.conj : L' →* MulAut L').range A =
      (ggTorusInduced τ).map (MulAut.congr Θ).toMonoidHom := by
  refine le_antisymm ?_ ?_
  · intro v hv
    obtain ⟨c, ⟨n, rfl⟩, hcN, hvc⟩ := mem_ggAutomizer_iff.mp hv
    have hv' : v = ggConjAut A hcN := MulEquiv.ext fun a => Subtype.ext (hvc a)
    obtain ⟨u, hu, hnu⟩ := hnorm n hcN
    have hs : ∀ f, ψ n * ψ (σ f) * (ψ n)⁻¹ = ψ (σ (u f)) :=
      fun f => by simpa only [hψσ] using hnu f
    obtain ⟨hn, hcongr⟩ := exists_ggConjAut_eq_congr hker Θ hΘ hs
    refine Subgroup.mem_map.mpr ⟨u, hu, ?_⟩
    have hproof : hn = hcN := Subsingleton.elim _ _
    rw [hproof] at hcongr
    exact hcongr.symm.trans hv'.symm
  · rintro v ⟨u, hu, rfl⟩
    obtain ⟨g, hg⟩ := mem_ggTorusInduced.mp hu
    obtain ⟨m, rfl⟩ := hψ g
    have hs : ∀ f, ψ m * ψ (σ f) * (ψ m)⁻¹ = ψ (σ (u f)) :=
      fun f => by simpa only [hψσ] using hg f
    obtain ⟨hmN, hmeq⟩ := exists_ggConjAut_eq_congr hker Θ hΘ hs
    exact hmeq ▸ ggConjAut_mem_ggAutomizer (H := (MulAut.conj : L' →* MulAut L').range)
      (Bs := A) (g := MulAut.conj m) ⟨m, rfl⟩ hmN

end Transfer

end CFSG.StandardType

end
