module

public import CFSG.RankThree.PartOne.CTP.SporadicNoncomm
public import Certificates.Certificate9486
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.RankThree.PartOne.StrongP CFSG.Blueprint

theorem fi24_sylow7_check :
    (ops3 781).cubicCheck fi24Sylow7Data = true :=
  Certificates.certificate9486

theorem hasNoncommPair_Fi24_seven :
    HasNoncommPair 7 (NativeSporadic.Carrier .Fi24Prime) := by
  obtain ⟨x, y, -, hx, hy, hz, -, -, hc, -⟩ :=
    (spec3 781).cubic_of_check fi24Sylow7Data fi24_sylow7_check
  exact hasNoncommPair_of_cubic (by norm_num) hx hy hz hc

end CFSG.RankThree.PartOne.CTP
