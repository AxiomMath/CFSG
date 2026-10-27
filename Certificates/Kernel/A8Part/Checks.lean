module

public import Certificates.Kernel.A8Part.Data
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelA8Part

set_option maxRecDepth 100000

theorem ch7154t : tOK = true := by quickRfl

theorem ch7154u : uOK = true := by quickRfl

#kc_each ch7154m 0 3

theorem ch7154L1 : memOK 1 3 0 1890 = true := by quickRfl

theorem ch7154L2 : memOK 2 3 3 1902 = true := by quickRfl

theorem ch7154L3 : memOK 3 3 6 1914 = true := by quickRfl

theorem ch7154L4 : memOK 4 9 9 1926 = true := by quickRfl

theorem ch7154L5 : memOK 5 21 18 1962 = true := by quickRfl

theorem ch7154L6 : memOK 6 21 39 2046 = true := by quickRfl

theorem ch7154s1 : subOK 1 3 1 0 0 0 = true := by quickRfl

theorem ch7154s2 : subOK 2 3 1 3 3 1 = true := by quickRfl

theorem ch7154s3 : subOK 3 3 1 6 6 2 = true := by quickRfl

theorem ch7154s4 : subOK 4 9 2 9 9 3 = true := by quickRfl

theorem ch7154s5a : subOK 5 3 1 18 27 5 = true := by quickRfl

theorem ch7154s5b : subOK 5 7 1 21 30 6 = true := by quickRfl

theorem ch7154s6a : subOK 6 3 1 28 37 7 = true := by quickRfl

theorem ch7154s6b : subOK 6 7 1 31 40 8 = true := by quickRfl

theorem ch7154s7a : subOK 7 9 2 38 47 9 = true := by quickRfl

theorem ch7154s7b : subOK 7 5 1 47 65 11 = true := by quickRfl

theorem ch7154s7c : subOK 7 7 1 52 70 12 = true := by quickRfl

theorem ch7154repM : repMOK = true := by quickRfl

theorem ch7154rep : repOK = true := by quickRfl

theorem ch7154join : joinOK = true := by quickRfl

theorem ch7154top : topOK = true := by quickRfl

theorem ch7154rs : rsOK = true := by quickRfl

theorem ch7154k : kOK = true := by quickRfl

theorem ch7154h : hOK = true := by quickRfl

theorem ch7154sy : syOK = true := by quickRfl

#kc_each ch7154pat 0 7

#kc_each ch7154cand 0 7

#kc_each ch7154ga 0 6

#kc_each ch7154gt 0 6

end CertificateChecks.KernelA8Part

end
