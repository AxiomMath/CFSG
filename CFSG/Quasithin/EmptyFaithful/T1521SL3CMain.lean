module

public import CFSG.Quasithin.EmptyFaithful.T1521SL3CVac
public import CFSG.Quasithin.EmptyFaithful.T1521SL3ECovMain

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

theorem dich1521L3_of_parts (hE : E1L3) (hEc : E1L3Cover) (hA : AutFactL3) : Dich1521L3 := by
  intro G _ _ X S L hStd hCM hco hZ hty
  refine Or.inl (nrm1521_of_inner ?_ ?_)
  · rcases hty with hL | hQ
    · exact hE G X S L hStd hco hZ hL
    · by_cases hEA : ∀ z ∈ Subgroup.center ↥L, z ^ 2 = 1
      · exact hEc G X S L hStd hco hZ ⟨2, by norm_num, hQ⟩ hEA
      · exact (l3cover_nonElem_false hStd hco hZ hQ hEA hCM).elim
  · intro v hvS hvN hc l hl
    exact hA G L (S ⊓ L) hco.2.2 hZ hty hStd.sylowL v hvN
      (hStd.sylow.2.1.to_le (Subgroup.zpowers_le.mpr hvS)) hc l hl

end CFSG.Quasithin
