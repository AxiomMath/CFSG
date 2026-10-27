module

public import CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOneModuleData
import Certificates.Kernel.Misc.Ext3362

public section

namespace Certificates

open CFSG.LocalAnalysis.ComponentInitial.ChevSp6EpsOne.ExtOne in
theorem certificate3362 : extCheck = true :=
  CFSG.KC.Misc.Ext.extCheck_eq ▸ CFSG.KC.Misc.Ext.c3362_sound CFSG.KD.Misc.Ext3362.check

end Certificates
