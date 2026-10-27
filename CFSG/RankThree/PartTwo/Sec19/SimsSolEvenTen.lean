module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenRSmall
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenLen2
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenHighN
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenTI

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

theorem evenN_ten_of_node
    (hNode : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hST : CFSG.CGT.PushingUpLit.SolK.SolomonTimmesfeldTight) : EvenN 10 := by
  intro G _ _ M X S
  obtain ⟨C⟩ := exists_cfg_of_setting S
  obtain ⟨D⟩ := C.exists_piData (by norm_num) (by decide)
  rcases C.card_Rc_le_two D rfl hST hNode with h | hR
  · exact h
  · exact Cfg.PiData.inCatalog_of_centInM hNode C D hR
      (Cfg.PiData.centInM_ten_of D hR (fun x hl => D.centralizer_le_M_of_len_two hR x hl)
        (fun x hl => D.centralizer_le_M_of_len_four hR x hl))

theorem evenN_ten
    (hST : CFSG.CGT.PushingUpLit.SolK.SolomonTimmesfeldTight) : EvenN 10 :=
  evenN_ten_of_node SolSeven.nodeStatement_holds hST

end CFSG.RankThree.PartTwo.Sec19.SolEven
