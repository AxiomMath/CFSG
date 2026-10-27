module

public import CFSG.Quasithin.Background.P4InspOrthBasic
public import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusSixExtract

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

namespace G11

namespace P4InspOrth

open CFSG.GroupTheory.WeirSylow

section Minus6

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U] {f : LinearMap.BilinForm (ZMod 2) U}
  {q : U → ZMod 2}

theorem p4insporth_simple_minus_six [Finite U] (hf : IsSymplectic f)
    (hq : ∀ x y, q (x + y) = q x + q y + f x y) (hdim : Module.finrank (ZMod 2) U = 6)
    (hminus : ¬ IsPlusType (p4insporth_quad hq)) : IsSimpleGroup ↥⁅orthSub q, orthSub q⁆ := by
  have : FiniteDimensional (ZMod 2) U := Module.Finite.of_finite
  have hts : ∀ S : Submodule (ZMod 2) U, Module.finrank (ZMod 2) S = 3 →
      ∃ u ∈ S, p4insporth_quad hq u ≠ 0 := by
    intro S hS
    by_contra h
    push Not at h
    exact hminus ⟨S, by omega, h⟩
  obtain ⟨E, _, _, D, ψ, ρ, -, -, -, -, hcomm, hs, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_six_actual_derived_extraction (p4insporth_quad hq)
      (p4insporth_nondegenerate_quad hf hq) hdim hts
  rw [p4insporth_orthogonalGroup_quad hq] at hcomm
  rw [hcomm]
  exact hs

end Minus6

end P4InspOrth

end G11

end CFSG.Quasithin
