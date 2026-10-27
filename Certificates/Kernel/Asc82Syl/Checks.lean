module

public import Certificates.Data.Kernel.Asc82Syl.Defs
public import Certificates.Kernel.Asc82Syl.Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KD.Asc82Syl

theorem ch442274_consts : constsK = true := by quickRfl

theorem ch442274_genP : genK gP dP = true := by quickRfl

theorem ch442274_enumP : enumK wpP gP = true := by quickRfl

theorem ch442274_keyP : keyK wpP pP 512 = true := by quickRfl

theorem ch442274_relP : relK wpP 5 9 rlP = true := by quickRfl

theorem ch442274_qtP : qtK wpP qmP qfP 5 16 = true := by quickRfl

theorem ch442274_ctP : ctK wpP ctP 5 16 = true := by quickRfl

theorem ch442274_omP : omK wpP omP 5 = true := by quickRfl

theorem ch442274_famP : famK fmP qmP ctP omP 5 16 32 false = true := by quickRfl

theorem ch442274_genM : genK gM dM = true := by quickRfl

theorem ch442274_enumM : enumK wpM gM = true := by quickRfl

theorem ch442274_keyM : keyK wpM pM 1024 = true := by quickRfl

theorem ch442274_relM : relK wpM 6 10 rlM = true := by quickRfl

theorem ch442274_qtM : qtK wpM qmM qfM 6 16 = true := by quickRfl

theorem ch442274_ctM : ctK wpM ctM 6 16 = true := by quickRfl

theorem ch442274_omM : omK wpM omM 6 = true := by quickRfl

theorem ch442274_famM : famK fmM qmM ctM omM 6 16 32 true = true := by quickRfl

end CFSG.KD.Asc82Syl

end
