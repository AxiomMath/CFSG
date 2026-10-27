module

public import Certificates.Kernel.A7Lat.Data
import CFSG.Certificates.Kernel.Common.Each
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelA7Lat

set_option maxRecDepth 100000

theorem ch7250t : tOK = true := by quickRfl

theorem ch7250u : uOK = true := by quickRfl

#kc_each ch7250m 0 3

theorem ch7250L1 : memOK 1 3 0 630 = true := by quickRfl

theorem ch7250L2 : memOK 2 3 3 639 = true := by quickRfl

theorem ch7250L3 : memOK 3 3 6 648 = true := by quickRfl

theorem ch7250L4 : memOK 4 3 9 657 = true := by quickRfl

theorem ch7250L5 : memOK 5 3 12 666 = true := by quickRfl

theorem ch7250L6 : memOK 6 9 15 675 = true := by quickRfl

theorem ch7250L7 : memOK 7 15 24 711 = true := by quickRfl

theorem ch7250L8 : memOK 8 21 39 756 = true := by quickRfl

theorem ch7250L9 : memOK 9 21 60 819 = true := by quickRfl

theorem ch7250L10 : memOK 10 45 81 882 = true := by quickRfl

theorem ch7250s1 : subOK 1 3 1 0 0 0 = true := by quickRfl

theorem ch7250s2 : subOK 2 3 1 3 3 1 = true := by quickRfl

theorem ch7250s3 : subOK 3 3 1 6 6 2 = true := by quickRfl

theorem ch7250s4 : subOK 4 3 1 9 9 3 = true := by quickRfl

theorem ch7250s5 : subOK 5 3 1 12 12 4 = true := by quickRfl

theorem ch7250s6 : subOK 6 9 2 15 15 5 = true := by quickRfl

theorem ch7250s7a : subOK 7 3 1 24 33 7 = true := by quickRfl

theorem ch7250s7b : subOK 7 5 1 27 36 8 = true := by quickRfl

theorem ch7250s8a : subOK 8 3 1 32 41 9 = true := by quickRfl

theorem ch7250s8b : subOK 8 7 1 35 44 10 = true := by quickRfl

theorem ch7250s9a : subOK 9 3 1 42 51 11 = true := by quickRfl

theorem ch7250s9b : subOK 9 7 1 45 54 12 = true := by quickRfl

theorem ch7250s10a : subOK 10 9 2 52 61 13 = true := by quickRfl

theorem ch7250s10b : subOK 10 5 1 61 79 15 = true := by quickRfl

theorem ch7250s11a : subOK 11 9 2 66 84 16 = true := by quickRfl

theorem ch7250s11b : subOK 11 5 1 75 102 18 = true := by quickRfl

theorem ch7250s11c : subOK 11 7 1 80 107 19 = true := by quickRfl

theorem ch7250repM : repMOK = true := by quickRfl

theorem ch7250rep : repOK = true := by quickRfl

theorem ch7250join : joinOK = true := by quickRfl

theorem ch7250top : topOK = true := by quickRfl

end CertificateChecks.KernelA7Lat

end
