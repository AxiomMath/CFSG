module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolSevenTI
public import CFSG.RankThree.PartTwo.Sec19.SimsSolSevenTight

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolSeven

theorem inCatalog_of_setting
    (hST : CFSG.CGT.PushingUpLit.SolK.SolomonTimmesfeldTight)
    {G : Type} [Group G] [Finite G] {M X : Subgroup G} (S : Setting G M X) :
    CFSG.Assembly.InCatalog G := by
  rcases inCatalog_or_tightData hST S S.card_blockU
      (fun _ hw hc => S.eq_one_of_mem_W_of_mem_C hw hc) with h | ⟨hRab, hR2⟩
  · exact h
  · have := S.simple
    obtain ⟨B, hB, h4, hTI, hWC⟩ := S.exists_ti hRab hR2
    exact inCatalog_of_listGroup (nodeStatement_holds G S.nonab B hB h4 hTI hWC)

theorem lit316SolomonSeven_of_tight
    (hST : CFSG.CGT.PushingUpLit.SolK.SolomonTimmesfeldTight) : Lit316SolomonSeven :=
  lit316SolomonSeven_of_setting fun _ _ _ _ _ S => inCatalog_of_setting hST S

end CFSG.RankThree.PartTwo.Sec19.SolSeven
