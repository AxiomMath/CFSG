module

public import Certificates.Kernel.Co1M.K45D
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.Co1M

theorem k45_se : se45K 1 SE45 = true := by quickRfl

theorem k45_ce : ce45K 1 CE45 = true := by quickRfl

theorem k45_hd : hd45K SE45 CE45 = true := by quickRfl

theorem k45_t4s : t45K 1 SE45 = true := by quickRfl

theorem k45_t4c : t45K 1 CE45 = true := by quickRfl

end CFSG.KD.Co1M

end
