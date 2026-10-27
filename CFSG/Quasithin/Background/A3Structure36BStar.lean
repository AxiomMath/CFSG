
module

public import CFSG.Quasithin.Background.A3Structure36BStarBase

public import CFSG.Quasithin.Background.A3Structure36BSetup
public import CFSG.Quasithin.Background.A3Structure36BPrime

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.A36B

open scoped commutatorElement

variable {X : Type} [Group X]

theorem a36_extra (hF : A36CaseBFacts) (h : A36BHyp X) : A36Extra X := by
  obtain ⟨K, hK⟩ := exists_kernelSetup hF h
  intro q hq hqF
  obtain ⟨D, hDK⟩ := hK.prime q hq (isPi_of_dvd_card_fitting hF h hK hq hqF)
  refine ⟨D.P, D.supercritical, D.faithful, D.iso, fun x => ?_⟩
  have hx := D.mem_K_iff x
  rw [hDK, kernel_eq_fitting h hK] at hx
  exact hx.symm

end CFSG.Quasithin.A36B
