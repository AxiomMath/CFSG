module

public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrConfigAStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrConfigC
public import CFSG.RankThree.GF2n.Stroth80.Sec41iiTensorSetupOfModel

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped Matrix


theorem sec715Irr_of_configs (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h310chi : Stroth310ChiStatement) (h51 : Stroth51Statement) (h52a : Stroth52aStatement)
    (h52b : Stroth52bStatement) (hNO : Sec7NOrderStatement) (hA : Sec7AExistsStatement)
    (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement) (hMp : Sec7CentreMpStatement)
    (hZV : Sec7ZVStatement) (hCommN : Sec7CommNStatement) (hCRW : Sec7CRWStatement)
    (hY : Sec713YStatement) (hCent : Sec715CentStatement) (hConj : Sec715ConjStatement)
    (hConfig : Sec715LayerConfigStatement) (hIrrA : Sec715IrrConfigAStatement) :
    Sec715IrrStatement := by
  intro G _ _ M Q Z B _ hc n t hs hp hn Z0 hZ0 hZN hTI A hZA hAN hAk
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  obtain ⟨m, γ, M₀, -, hM⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨ρ, b, hS⟩ := hc.exists_isTensorSetup h34 hs.toSec5.width hs.toSec5.n_gt
    hs.toSec5.noA2 hs.toSec5.gen hM
  obtain ⟨φ₈, e, hφr, hφk, he⟩ := exists_phi8 hS hs.toSec5.mem hp
  rcases hConfig G M Q Z B hc n t hs hp hn Z0 hZ0 hZN _ γ M₀ ρ b hS φ₈ hφr hφk e he with
    hCA | hCC
  · exact hIrrA G M Q Z B hc n t r hs hr hp hn Z0 hZ0 hZN _ γ M₀ ρ b hS φ₈ hφr hφk e he hTI hCA A
      hZA hAN hAk
  · exact (false_of_isLayerConfigC h34 h310chi h51 h52a hA hZt hZcard hMp hZV hCommN hCRW hMp hY
      hCent hConj hS hs hr hp hn hZ0 hZN hTI
      (fun f hf => (mem_deltaSub_iff h34 hRoot h310chi h51 h52a h52b hNO hZcard hCRW hMp hS hs
        hr).mp hf) hCC).elim

end CFSG.RankThree.GF2n.Stroth80.S715L
