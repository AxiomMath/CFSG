module

public import CFSG.Timmesfeld.ARS.Sec8HypDegenLevi
public import CFSG.Timmesfeld.ARS.InductionMax

public section

namespace CFSG.Timmesfeld.ARS

theorem degenerate813Input : Degenerate813Input := by
  intro G _ R h A hA _ hAne _ A₀ hA₀ Δ hΔ hdeg E hE E' hE' hEE'
  obtain ⟨E₀, hE₀, rfl⟩ := hΔ
  exact Levi.eq_of_commuting_iff_of_degenerate h hA hAne hA₀ hE₀ hdeg hE hE' hEE'

end CFSG.Timmesfeld.ARS
