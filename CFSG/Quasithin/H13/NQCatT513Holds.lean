module

public import CFSG.Quasithin.H13.NQCatT513PSL2
public import CFSG.Quasithin.H13.NQCatT513L35
public import CFSG.Quasithin.H13.NQCatT513U35

public section

namespace CFSG.Quasithin.H13.NQCat.T513

theorem factType513Aut_holds :
    H13.FactType513Aut := by
  intro A _ _ Q R S B D h hQ
  rcases hQ with hQ | hQ | ⟨s, hs⟩
  · exact normalizer_of_psl2 h (Or.inl hQ)
  · exact normalizer_of_psl2 h (Or.inr hQ)
  · cases s
    · exact normalizer_of_psu35 h hs
    · exact normalizer_of_psl35 h hs

end CFSG.Quasithin.H13.NQCat.T513
