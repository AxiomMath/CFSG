module

public import Certificates.Kernel.Co1M.K45D
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Co1M

theorem k39_se : se45K 2 SE39 = true := by quickRfl

theorem k39_ce : ce45K 2 CE39 = true := by quickRfl

theorem k39_hd : hd45K SE39 CE39 = true := by quickRfl

theorem k39_t4s : t45K 2 SE39 = true := by quickRfl

theorem k39_t4c : t45K 2 CE39 = true := by quickRfl

end CFSG.KD.Co1M

end
