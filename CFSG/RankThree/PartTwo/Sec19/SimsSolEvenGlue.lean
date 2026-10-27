module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenDefs
public import CFSG.RankThree.PartTwo.Sec19.F194Item316Leaves

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

theorem lit316SolomonEven_of_evenN (h6 : EvenN 6) (h8 : EvenN 8) (h10 : EvenN 10) :
    Lit316SolomonEven := by
  intro G _ _ hs hn hK hc he M X hM hB hab hN hu ⟨n, hmem, ht⟩ hcent
  have S : Setting G M X n := ⟨hs, hn, hK, hc, he, hM, hB, hab, hN, hu, ht, hmem, hcent⟩
  rcases hmem with rfl | rfl | rfl
  · exact h6 G M X S
  · exact h8 G M X S
  · exact h10 G M X S

end CFSG.RankThree.PartTwo.Sec19.SolEven
