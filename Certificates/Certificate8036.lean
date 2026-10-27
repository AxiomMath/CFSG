module

public import Certificates.Data.Item434SmallTwoIII
import Certificates.Kernel.Sp62.Final

public section

namespace Certificates

open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII in
theorem certificate8036 : pairsCheck8036 = true ∧ wreathCheck8036 = true ∧ centCheck8036 = true ∧
    hypCheck8036 = true :=
  ⟨CFSG.KD.Sp62.pairs_ok, CFSG.KD.Sp62.wreath_ok, CFSG.KD.Sp62.cent_ok, CFSG.KD.Sp62.hyp_ok⟩

end Certificates
