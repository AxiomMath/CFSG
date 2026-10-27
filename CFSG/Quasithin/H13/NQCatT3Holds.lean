module

public import CFSG.Quasithin.H13.NQCatT3A7
public import CFSG.Quasithin.H13.NQCatT3M22
public import CFSG.Quasithin.H13.NQCatT3M23
public import CFSG.Quasithin.H13.NQCatT3J1
public import CFSG.Quasithin.H13.NQCatT3J2
public import CFSG.Quasithin.H13.NQCatT3HS
public import CFSG.Quasithin.H13.NQCatT3Ru
public import CFSG.Quasithin.H13.NQCatT3J4

public section

namespace CFSG.Quasithin.H13.NQCat.T3

theorem factType513Three_of_j4
    (hJ4 : H13.FactType513ThreeJ4) : H13.FactType513Three := by
  intro A _ _ Q R S B D h hQ hD3 hnot
  rcases hQ with hA7 | hA7' | hM22 | hM22' | hM23 | hJ1 | hJ2 | hJ4' | hHS | hRu
  · exact ⟨Or.inl hA7, three_a7 h (Or.inl hA7) hD3⟩
  · exact ⟨Or.inr (Or.inl hA7'), three_a7 h (Or.inr hA7') hD3⟩
  · exact absurd (three_m22 h (Or.inl hM22) hD3) hnot
  · exact absurd (three_m22 h (Or.inr hM22') hD3) hnot
  · exact ⟨Or.inr (Or.inr (Or.inr hM23)), three_m23 h hM23 hD3⟩
  · exact absurd (three_j1 h hJ1 hD3) hnot
  · exact ⟨Or.inr (Or.inr (Or.inl hJ2)), three_j2 h hJ2 hD3 hnot⟩
  · exact absurd (hJ4 A Q R S B D h hJ4' hD3) hnot
  · exact absurd (three_hs h hHS hD3) hnot
  · exact absurd (three_ru h hRu hD3) hnot

end CFSG.Quasithin.H13.NQCat.T3
