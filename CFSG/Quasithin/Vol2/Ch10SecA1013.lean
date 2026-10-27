module

public import CFSG.Quasithin.Vol2.Ch10SecABasic
public import CFSG.Quasithin.Vol2.Ch10StatementsB

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique

theorem stmt10_1_3_of (h122 : Vol2Native.Lemma122A) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) : Stmt10_1_3 := by
  intro G _ _ T L I hyp p hp hp2 hdvd
  have hf := hyp.fsu.faithful
  have := hyp.fsu.simple
  have h := h122 G hyp.fsu.simple hyp.fsu.nonabelian
    (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke) (fsuM T L) L (pCoreOf_fsuM_ne_bot hf)
    (mem_cComp_fsuM hf.1) p hp hp2
    (ncard_conjSubgroupsBy_fsuM h37 h38 hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke hf
      hyp.not_normal) hdvd
  rw [conjClosure_fsuM] at h
  exact h

end CFSG.Quasithin.Vol2.Ch10.SecA
