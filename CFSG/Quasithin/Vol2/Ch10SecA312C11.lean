module

public import CFSG.Quasithin.Vol2.Ch10SecA312C10
public import CFSG.Quasithin.Vol2.Ch10SecA312C1
public import CFSG.Quasithin.Vol2.Ch10SecA312C2
public import CFSG.Quasithin.Vol2.Ch10SecA312C9

public section

namespace CFSG.Quasithin.Vol2.Ch10

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique A312C

theorem a312PairCent_of
    (hList : Vol2Native.A312ListFactsCat) (hStruct : A312PairCentStruct) : A312PairCent := by
  intro X _ _ hq hX ho2 T hT B₁ hB₁ B₂ hB₂ hne₁ hne₂ hne hN₁ hN₂ hc he
  by_cases hs : A312PairStructCase B₁
  · exact hStruct X hq hX ho2 T hT B₁ hB₁ B₂ hB₂ hne₁ hne₂ hne hN₁ hN₂ hc he hs
  obtain ⟨e⟩ := he
  have hK : SylowTest X B₁ := fun r k hr hr2 hk h1 h2 => by
    have : Fact r.Prime := ⟨hr⟩
    exact false_of_sylowPart hr2 hk (perfect_of_mem_cComp (show B₁ ∈ cComp (B₁ ⊔ T) from hB₁))
      (hc.trans inf_le_left) e h1 h2
  rcases hList X hq hX ho2 T hT B₁ hB₁ hne₁ with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact hs (Or.inl h)
  · exact hs (Or.inr (Or.inl h))
  · exact case4 hK h
  · exact case5 hK h
  · exact case6 hK h
  · exact case7 hK h
  · exact case8 hK hs h
  · exact case9 hK hs h
  · exact case10 hK h
  · exact case11 hK h
  · exact case12 hK h
  · exact case13 hK h
  · exact case14 hK h
  · exact case15 hK h
  · exact hs (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact case17 hK h
  · exact case18 hK hs h
  · exact case19 hK hs h
  · exact case20 hK hs h

end CFSG.Quasithin.Vol2.Ch10
