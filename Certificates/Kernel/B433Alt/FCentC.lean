module

public import Certificates.Kernel.B433Alt.FCentOK
import CFSG.Certificates.Kernel.BabyMonster.LoadRange

set_option maxRecDepth 100000

public section

#bm_range CFSG.KD.B4AZ step 0 43 stepChk

theorem CFSG.KD.B4AZ.ord_ok : CFSG.KD.B4AZ.ordChk = true := by decide +kernel

end
