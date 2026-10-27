module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512Cases
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512WrLin
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512WrUni

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Subgroup

theorem asch80L3EpsWreathed_holds : Asch80L3EpsWreathed := by
  intro Y _ _ E T p f hE _ hp2 hcase _ hT
  have := hE
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTi : ¬ 2 ∣ T.index := by
    have h := hT.2.2
    rwa [relIndex_top_right] at h
  set S : Sylow 2 Y := hT.2.1.toSylow hTi
  rcases hcase with ⟨h, hq⟩ | ⟨h, hq⟩
  · have hst := h.statedClassicalModel (by decide)
    have hEs := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 p f hst).2
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.KGroups.L3Eps.exists_projectiveSL_equiv hst
    exact Asch80Wr.not_exists_max_of_model hEs S e
      (Asch80Wr.wrModel_projectiveSL (by omega) (by omega))
  · have hst := h.statedClassicalModel (by decide)
    have hEs := (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 p f hst).2
    obtain ⟨K, _, hU, ⟨e⟩⟩ := CFSG.GH74.KGroups.L3Eps.exists_unitary_quotient_equiv hst
    exact Asch80Wr.not_exists_max_of_model hEs S e (Asch80Wr.wrModel_psu hU hp2 hq)

end CFSG.LocalAnalysis.WeakClosure81
