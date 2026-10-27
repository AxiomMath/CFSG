module

public import CFSG.Quasithin.Vol2.GoldschmidtEnd1222Basic
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitL52Rep

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

namespace End1222

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Quasithin.JonesParshall.Curtis

theorem exists_fixed_of_wedge
    {W : Type} [CommGroup W] [Finite W] (h2 : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 2 ^ 10)
    {H : Subgroup (MulAut W)} (φ : ↥H ≃* G5)
    (hirr : ∀ J : Subgroup W, (∀ h ∈ H, ∀ w ∈ J, (h : MulAut W) w ∈ J) → J = ⊥ ∨ J = ⊤)
    {c : MulAut W} (hc : ∀ g ∈ H, c * g = g * c) : ∃ v : W, v ≠ 1 ∧ c v = v := by
  obtain ⟨e, γ, he1, hγ⟩ := H13.Orbit.exists_wedge_coords h2 hcard φ hirr
  set v₀ : W := e.symm e01 with hv₀
  have hev₀ : e v₀ = e01 := e.apply_symm_apply _
  have hv₀1 : v₀ ≠ 1 := fun h => e01_ne (by rw [← hev₀, h, he1])
  refine ⟨v₀, hv₀1, ?_⟩
  have hfixU : e (c v₀) ∈ fixU wedgeRep := by
    intro u hu
    obtain ⟨h, rfl⟩ := γ.surjective u
    have hh : (h : MulAut W) v₀ = v₀ := by
      apply e.injective
      rw [hγ h v₀, hev₀]
      exact e01_mem_fixU _ hu
    rw [← hγ h (c v₀), ← comm_apply hc h.2 v₀, hh]
  have hne : e (c v₀) ≠ 0 := by
    intro h0
    have h1 : c v₀ = 1 := e.injective (h0.trans he1.symm)
    exact hv₀1 (c.injective (h1.trans (map_one c).symm))
  rcases wedge_fix hfixU with h0 | h1
  · exact absurd h0 hne
  · apply e.injective
    rw [h1, hev₀]

end End1222

end CFSG.Quasithin.H13
