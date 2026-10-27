module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordDExclQTwoClGlobal
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordDExclQTwoClSplit
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordDExclQTwoClMarking
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordDExclQTwoClFrame
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordDExclQTwoClTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly


theorem ggSecFiveBCoordDExclRestOn_qTwoCl (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) :
    GGSecFiveBCoordDExclRestOn fun _ lab => GGQTwoClLabel lab := by
  intro G _ _ p B Bs x L D J 𝒦 hR hp3 n eta i0 hn hK y K hKmem hnb r hr _ ⟨i, hri⟩ hlab
  subst hp3
  have hcfg := hR.1.1
  have hBs : IsElemAbelian 3 Bs := hcfg.2.1.2.1
  have hZ3 := not_three_dvd_card_center_of_qTwoCl hlab
  have hsplit := exists_mul_of_qTwoCl hcfg.2.1 hlab hZ3
  have hEab : IsElemAbelian 3 (Bs.subgroupOf K) := hBs.subgroupOf K
  obtain ⟨t, ht, hF⟩ := ggQTwoClFrameIn_of_marking hlab.subgroupOf hEab
    (mem_subgroupOf_of_mem_centralizer_subgroupOf hcfg.2.1.2.2.2 hsplit) hZ3
    (hcfg.three_pow_three_le_card_subgroupOf hnb hsplit)
  exact hR.ne_dCoordinateBlock_of_qTwoClLocal hLB hP (by omega) eta i0 hK hKmem hnb hr hri
    (ggQTwoClLocal_of_frameIn hBs hsplit hZ3 ht hF)

theorem ggSecFiveBCoordDExclRestInput_of_qTwoCl (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) : GGSecFiveBCoordDExclRestInput := by
  intro G _ _ p B Bs x L D J 𝒦 hR hp3 n eta i0 hn hK y K hKmem hnb r hr hrefl hsgn hlab
  refine ggSecFiveBCoordDExclRestOn_qTwoCl hLB hP G p B Bs x L D J 𝒦 hR hp3 n eta i0 hn hK y K
    hKmem hnb r hr hrefl hsgn (hlab.mono_label fun lab h => ⟨?_, h.2.2⟩)
  rw [h.2.1]
  exact one_lt_two

end CFSG.StandardType

end
