module

public import CFSG.Quasithin.Background.B4ModelsIso

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

theorem FFModel.RealizesVia.injective_of_faithful_on {V : Type*} [CommGroup V] {D : FFModel}
    (hD : D.Faithful) {H : Subgroup (MulAut V)} {U Z : Subgroup V} {π : D.Gam →* ↥H}
    (h : D.RealizesVia H U Z π) : Function.Injective π := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  obtain ⟨-, -, -, hHU, -, hsec, -, β, hβs, hβk, hβe⟩ := h
  apply hD
  intro m hm
  obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk ⟨m, hm⟩)
  have hact : D.act γ m ∈ D.sec := hsec γ m hm
  have hu' : ((π γ : ↥H) : MulAut V) (u : V) ∈ U := hHU (π γ) u u.2
  have h1 := hβe γ u ⟨m, hm⟩ hu' hact hu
  have h2' : ((π γ : ↥H) : MulAut V) (u : V) = (u : V) := by rw [hγ]; rfl
  have h2 : (⟨((π γ : ↥H) : MulAut V) (u : V), hu'⟩ : ↥U) = u := Subtype.ext h2'
  rw [h2, hu] at h1
  have h3 := QuotientGroup.eq.mp h1
  have h4 : m⁻¹ * D.act γ m ∈ D.ker := h3
  rw [mul_comm]
  exact h4

end CFSG.Quasithin
