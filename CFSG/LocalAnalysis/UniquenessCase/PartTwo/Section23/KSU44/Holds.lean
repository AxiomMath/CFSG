module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsNineK
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KSU44.Adapted
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KSU44.Transport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open KSUE

theorem kSU44_holds : KSU44 := by
  intro W _ _ H _ hNat S
  obtain ⟨K, _, _, hcard, hreal⟩ := hNat
  have hK : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 2 K :=
    ⟨Nat.prime_two, by norm_num, by rw [hcard]; norm_num⟩
  obtain ⟨Φ, e, he, hS⟩ := exists_adapted_equiv hK hreal S
  show Concl (S : Subgroup ↥H) (KTabD.pointStab H S) (fixSub H S)
  exact concl_of_adapted hK Φ e he S hS

end CFSG.LocalAnalysis.UniquenessCase.UC22
