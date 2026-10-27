module

public import CFSG.RankThree.PartTwo.Sec19.Item19ResProofSplit
public import CFSG.RankThree.PartTwo.Sec19.Item19Res2ProofSplitG2
import CFSG.RankThree.PartTwo.Sec19.Item19Res2ProofSplitL3
import CFSG.RankThree.PartTwo.Sec19.Item19Res2ProofSplitSp4
import CFSG.RankThree.PartTwo.Sec19.Item19Res2ProofSplitU48

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

namespace Item19Res2Proof

theorem ks1919SplitAut :
    KS1919SplitAut := by
  intro Y _ _ hY E hE hE27 F hFE hFinn hF9 c hcE hcF P hP
  rcases hY with ⟨n, hn, ⟨hne, ⟨ψ⟩⟩ | hSp4 | hG⟩ | hU48
  · exact ks1919SplitAut_psl hn hne ψ E hE hE27 F hFE hFinn hF9 c hcE hcF P hP
  · obtain ⟨ψ⟩ := hSp4
    exact ks1919SplitAut_sp4 ψ E hE hE27 F hFE hFinn hF9 c hcE hcF P hP
  · exact ks1919SplitAut_g2 hn hG E hE hE27 F hFE hFinn hF9 c hcE hcF P hP
  · obtain ⟨ψ⟩ := hU48
    exact ks1919SplitAut_u48 ψ E hE hE27 F hFE hFinn hF9 c hcE hcF P hP

theorem step1919CoreSplitLieRest :
    Step1919CoreSplitLieRest :=
  Item19ResProof.step1919CoreSplitLieRest_of ks1919SplitAut

end Item19Res2Proof

end CFSG.RankThree.PartTwo.Sec19
