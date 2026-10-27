module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsEleven
import CFSG.RankThree.PartTwo.KFacts.AutPSUInnDiag
import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

theorem kOutDiagU3_holds : KOutDiagU3 := by
  intro X _ _ a hU3 α β
  have hn : 2 ≤ a := CFSG.LocalAnalysis.EvenBN.GMSK.two_le_of_lieModel_PSU3 hU3
  obtain ⟨-, K, hField, hFin, hK, ⟨e₁⟩⟩ :=
    CFSG.LocalAnalysis.EvenBN.GMSK.statedClassicalModel_of_lieModel_PSU3 hU3
  let hu : @UnitaryFieldData 2 a K hField :=
    ⟨Nat.prime_two, by omega, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq : 2 < 2 ^ a := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hn
  let e : X ≃* @unitaryPSU 2 a K hField hu 3 :=
    e₁.trans (@unitaryPSUEquiv 2 a K hField hu 3 (by norm_num : 1 ≤ 3)).symm
  have hmem := CFSG.RankThree.PartTwo.KFacts.commutator_mem_range_psuConj hu hq
    (MulAut.congr e α) (MulAut.congr e β)
  have hmap := Subgroup.mem_map_of_mem (MulAut.congr e.symm).toMonoidHom hmem
  convert CFSG.RankThree.PartTwo.KFacts.map_range_psuConj_le_innDiagSubgroup hu e hmap
    using 1
  ext x
  simp [e, MulAut.congr_apply]

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
