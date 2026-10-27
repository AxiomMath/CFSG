module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Orbit

@[expose] public section

public section

namespace CFSG.StandardType.F4ExplicitPos.CommonFactor

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

open CFSG.HardMathSupport.Timmesfeld.LangTorus

variable {Ω : Type} [Field Ω]

theorem rationalRoots_eq_componentRoots_of_orbitLength_one {τ : Tag}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* Ωˣ}
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} (i : KernelComponent χ)
    (h1 : componentOrbitLength ρ (componentRoots χ i) = 1) :
    rationalRoots ρ χ i = componentRoots χ i := by
  have hne : {s : ℕ | 0 < s ∧
      (ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots χ i = componentRoots χ i}.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have h0 : componentOrbitLength ρ (componentRoots χ i) = 0 := by
      unfold componentOrbitLength
      rw [hemp, Nat.sInf_empty]
    rw [h1] at h0
    exact Nat.one_ne_zero h0
  have himg : (ρ : (Fin τ.rank → ℤ) → _)^[1] '' componentRoots χ i = componentRoots χ i := by
    rw [← h1]
    exact (Nat.sInf_mem hne).2
  rw [Function.iterate_one] at himg
  ext γ
  constructor
  · rintro ⟨k, δ, hδ, rfl⟩
    induction k with
    | zero => simpa using hδ
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact himg ▸ Set.mem_image_of_mem (ρ : (Fin τ.rank → ℤ) → _) ih
  · intro hγ
    exact ⟨0, γ, hγ, rfl⟩

end CFSG.StandardType.F4ExplicitPos.CommonFactor

end

end
