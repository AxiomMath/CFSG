module

public import CFSG.Quasithin.H13.L32ACSkPfB
public import CFSG.RankThree.PartTwo.KFacts.AutSz
public import CFSG.Quasithin.Vol2.GoldschmidtF134OddSz
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.H13.L32A.C.SkPf

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

theorem n2Model_n4Model_of_isSz {M : Type} [Group M] {n : ℕ}
    (h : IsSz n M) : N2Model M ∧ N4Model M := by
  obtain ⟨-, a, ha, K, _, _, hn, hK, ⟨e⟩⟩ := h
  subst hn
  have hZ := CFSG.Quasithin.H13.NQCore.center_suzukiGroup_eq_bot ha hK
  have h2 := n2Model_n4Model_of_two_inner hZ fun α hα =>
    mem_range_conj_of_pow_two_pow (CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.szFieldAut a K)
      (CFSG.RankThree.PartTwo.KFacts.exists_conj_mul_szFieldAut ha hK)
      (fun β hβ => CFSG.RankThree.Automorphisms.eq_one_of_szFieldAut_mem_inner ha hK hβ)
      (f := 2 * a + 1) ⟨a, rfl⟩ (ringAut_pow_eq_one hK) hα
  exact ⟨h2.1.of_mulEquiv e.symm, h2.2.of_mulEquiv e.symm⟩

end CFSG.Quasithin.H13.L32A.C.SkPf
