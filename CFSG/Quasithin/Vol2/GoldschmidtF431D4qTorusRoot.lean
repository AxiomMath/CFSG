module

public import CFSG.LieType.Steinberg.CentralExt.TrialityLift

public section

namespace CFSG.Quasithin.H13.F431.D4q.F48

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.LieType.Steinberg.CentralExt.TrialityClosed


variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)

theorem tor_mem_torus (s : fixedUnits σ) (t : Kˣ) : tor hσ s t ∈ ⨆ i, hHat σ i := by
  have e : tor hσ s t =
      (⟨torusElement d4 K (nd 2) (s : Kˣ),
        hHatE_le_twistedGroup hσ (ng 0) (torusElement_mem_hHatE s)⟩ : twistedGroup σ) *
      ⟨hShortHom σ t, hHatE_le_twistedGroup hσ (ng 1) (hShortHom_mem_hHatE t)⟩ :=
    Subtype.ext rfl
  rw [e]
  exact Subgroup.mul_mem _
    (Subgroup.mem_iSup_of_mem (ng 0) (Subgroup.mem_subgroupOf.2 (torusElement_mem_hHatE s)))
    (Subgroup.mem_iSup_of_mem (ng 1) (Subgroup.mem_subgroupOf.2 (hShortHom_mem_hHatE t)))

theorem fix_short {α : Fin d4.rank → ℤ} (hα : IsRoot d4 α) (hne : rho α ≠ α) {γ : Fin 2 → ℤ}
    (hp : proj α = γ) (s : fixedUnits σ) (t : Kˣ) (hχ : chi σ s t α ≠ 1) {x : twistedGroup σ}
    (hx : x ∈ twistedRootGroup σ γ) (hfix : tor hσ s t * x * (tor hσ s t)⁻¹ = x) : x = 1 := by
  obtain ⟨c, rfl⟩ := (mem_iff_xS hσ hα hne hp x).1 hx
  rw [tor_conj_xS hσ hα hne s t c] at hfix
  have h1 : (chi σ s t α : K) * c = c := xOrbit_injective σ hα hne (congrArg Subtype.val hfix)
  have hc0 : c = 0 := by
    by_contra hc0
    exact hχ (Units.val_eq_one.1 (mul_right_cancel₀ hc0 (by rw [one_mul]; exact h1)))
  rw [hc0]
  exact Subtype.ext (xOrbit_zero σ _)

theorem fix_long {α : Fin d4.rank → ℤ} (hα : IsRoot d4 α) (hρ : rho α = α) {γ : Fin 2 → ℤ}
    (hp : proj α = γ) (s : fixedUnits σ) (t : Kˣ) (hχ : chi σ s t α ≠ 1) {x : twistedGroup σ}
    (hx : x ∈ twistedRootGroup σ γ) (hfix : tor hσ s t * x * (tor hσ s t)⁻¹ = x) : x = 1 := by
  obtain ⟨c, rfl⟩ := (mem_iff_xL hσ hα hρ hp x).1 hx
  rw [tor_conj_xL hσ hα hρ s t c] at hfix
  have h1 : (chi σ s t α : K) * (c : K) = c := by
    have := xPar_injective hα (congrArg Subtype.val hfix)
    rwa [Subfield.coe_mul] at this
  have hc0 : c = 0 := by
    by_contra hc0
    have hc0' : (c : K) ≠ 0 := fun h => hc0 (Subtype.ext h)
    exact hχ (Units.val_eq_one.1 (mul_right_cancel₀ hc0' (by rw [one_mul]; exact h1)))
  rw [hc0]
  exact Subtype.ext (by rw [xL_val]; exact xPar_zero _)

end CFSG.Quasithin.H13.F431.D4q.F48
