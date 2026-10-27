module

public import CFSG.OddTranspositions.TheoremTwo.ThirdKindExclusion
import CFSG.OddTranspositions.TheoremTwo.ConfigAssembly
import CFSG.OddTranspositions.TheoremTwo.LemmaFourFiveAlt

public section

namespace CFSG.OddTranspositions

theorem configStatement_holds :
    ConfigStatement := by
  intro G _ _ D hC hrad hL w v n htri hn h1n hord _ hB hQ
  exact exists_config_of_alt5 hC.setup hrad hL htri hn h1n hord hB hQ
    fun _ _ hperf hodd hB₁ hS' hS'K _ ha2 haS hfix =>
      alt5_and_outer_of_fix_center_inf hperf hodd hB₁ hS' hS'K ha2 haS hfix

end CFSG.OddTranspositions

end
