module

public import CFSG.SignalizerFunctorTheorem.Solvable.Completeness
public import CFSG.SignalizerFunctorTheorem.Glauberman.Steps678.Plus

public section

open CFSG.Open CFSG.SignalizerFunctor.Helpers

namespace CFSG.SignalizerFunctorTheorem.Glauberman

theorem Setting.false {G : Type*} [Group G] [Finite G] {p : ℕ} {A : Subgroup G}
    {θ : Subgroup G → Subgroup G} (h : Setting p A θ) : False := by
  obtain ⟨S, hS, hS0⟩ := Steps678.exists_maximal_prime h (q := 2) (Or.inl rfl)
  obtain ⟨T, hT, hT0⟩ := Steps678.exists_maximal_prime h (q := 3) (Or.inr rfl)
  obtain ⟨Z, B', x, z, hZS, hZc, hZA, hB', hx, hz, hxz⟩ :=
    Steps678.exists_plus h (q := 2) (r := 3) (Or.inl ⟨rfl, rfl⟩) hS hS0
  obtain ⟨Z', D', x', z', hZS', hZc', hZA', hD', hx', hz', hxz'⟩ :=
    Steps678.exists_plus h (q := 3) (r := 2) (Or.inr ⟨rfl, rfl⟩) hT hT0
  obtain ⟨W, hW, hWB, hWD⟩ :=
    Steps678.exists_Ek_le_inf_hyperplanes h.prime h.elementary h.large hB' hD'
  obtain ⟨H, hH, hWH⟩ := Steps678.exists_maximal_ge (Steps678.compat_value h hW)
  have hCAH : signalizerCommonFixed p 1 A θ ≤ H :=
    (Steps678.commonFixed_le_value hW).trans hWH
  obtain ⟨q₀, hq₀, hcore⟩ := Steps678.exists_primeCoreIn_eq_bot h hH hCAH
  rcases hq₀ with rfl | rfl
  · exact Steps678.final_step h (Or.inl rfl) hS hH hCAH hcore hZS hZc hZA
      (hWH (hx W hW hWB)) hz hxz
  · exact Steps678.final_step h (Or.inr rfl) hT hH hCAH hcore hZS' hZc' hZA'
      (hWH (hx' W hW hWD)) hz' hxz'

theorem twoThreeCase (p : ℕ) (hp : p.Prime) :
    CFSG.SignalizerFunctorTheorem.Solvable.TwoThreeCase p 1 := by
  intro G _ _ A hA hlarge θ hcond hloc hspec
  by_contra hinc
  exact (Setting.mk hp hA hlarge hcond hloc hspec hinc).false

end CFSG.SignalizerFunctorTheorem.Glauberman
