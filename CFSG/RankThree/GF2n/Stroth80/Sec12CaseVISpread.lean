module

public import CFSG.RankThree.GF2n.Stroth80.Sec12CaseVIMeet
public import CFSG.RankThree.GF2n.Stroth80.Sec12CaseVIClosure
public import CFSG.RankThree.GF2n.Stroth80.Sec12NoA2Spread

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank Matrix
open scoped commutatorElement

theorem caseVIMeet : CaseVIMeetStatement := by
  intro G _ _ M Q Z X B hcX hcB n hw hn hVI
  obtain ⟨m, γ, M₀, -, h⟩ := stroth_globalModelDataGF hcX.hyp
  obtain ⟨φ, hφπ, hφQ, hφiso⟩ := exists_actionHom_H0 hcX.hyp h
  obtain ⟨F, _, _, ρ', C, hrange, -, -⟩ := exists_natDualCoord hcX hw hn hVI h φ hφπ
  exact caseVIMeet_of_coord hcB hw hn (Lgen_le_H0 hcX)
    (le_trans le_sup_left (le_Lgen_self M (LB M Q X)))
    (fun m hm s hs => (Subgroup.mem_normalizer_iff.mp
      (Lgen_normalizes M (LB M Q X) hm) s).mp hs) h.card φ hφQ hφiso ρ' hrange C

theorem caseVIClosure : CaseVIClosureStatement := by
  intro G _ _ M Q Z X B hcX hcB n hw hn hVI hno
  obtain ⟨m, γ, M₀, -, h⟩ := stroth_globalModelDataGF hcX.hyp
  obtain ⟨φ, hφπ, hφQ, hφiso⟩ := exists_actionHom_H0 hcX.hyp h
  obtain ⟨F, _, _, ρ', C, hrange, hker, -⟩ := exists_natDualCoord hcX hw hn hVI h φ hφπ
  exact caseVIClosure_of_coord hcB hw hn hno (Lgen_le_H0 hcX) h φ hφπ hφQ hφiso ρ' hrange hker C

theorem strothNoA2Spread_of_h1111 (h1111 : Stroth1111Statement) : StrothNoA2SpreadStatement :=
  strothNoA2Spread_of_inputs h1111 caseVIMeet caseVIClosure

end CFSG.RankThree.GF2n.Stroth80
