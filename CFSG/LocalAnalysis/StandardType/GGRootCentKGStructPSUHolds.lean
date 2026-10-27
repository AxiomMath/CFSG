module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGStructPSU
import CFSG.LocalAnalysis.StandardType.GGRootCentKGStructPSUComm
import CFSG.LocalAnalysis.StandardType.GGRootCentKGStructPSUAct
import CFSG.LocalAnalysis.StandardType.GGRootCentKGStructPSUPerf

public section

namespace CFSG.StandardType

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

namespace KGPSU

variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem kgPiecesD_rootU (h : UnitaryFieldData 2 f K) {m : ℕ} (hm : 3 ≤ m) :
    KGND.KGPiecesD (AutPSU.inndiag h (n := m + 1))
      (AutPSU.projU h (AutPSU.rootU (K := K) (f := f) m)) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hk : 2 ≤ k := by omega
  by_cases hsmall : f = 1 ∧ k ≤ 3
  · exact KGND.kgPiecesD_of_isSolvable (isSolvable_centralizer_rootU h hsmall.1 hk hsmall.2)
  · have hkq : 4 ≤ k ∨ 2 ≤ f := by
      have := h.one_le
      omega
    exact KGND.kgPiecesD_of_decomp (pCoreOf_centralizer_rootU h hm)
      (radical_sup_suBlock_le_centralizer h hk) (commutator_centralizer_rootU_le h hk)
      (suBlock_le_normalizer_radical h hk) (radical_inf_suBlock h hk)
      (commutator_radical_sup_suBlock h hk hkq) (isQuasisimple_suBlock h hk hkq) _
      (largeEvenMarking_suBlock h hk hkq) fun _ hδ hδr => exists_suConjSet_of_fix h hk hδ hδr

end KGPSU

section Tag

theorem ggRootCentKGStructTag_PSU : GGRootCentKGStructTag .PSU :=
  ggRootCentKGStructTag_PSU_of fun _ _ _ _ _ _ h hm => KGPSU.kgPiecesD_rootU h hm

end Tag

end CFSG.StandardType

end
