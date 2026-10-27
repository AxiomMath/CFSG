module

public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerComp
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerMark
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentInnerOne

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType.Triality

namespace D4Inner

theorem ggD4InnerTwoMarkInput_holds : GGD4InnerTwoMarkInput := by
  intro K _ _ _ n hK hn s hs3 hd J hJ
  rcases (show n = 1 ∨ 3 ≤ n by obtain ⟨m, rfl⟩ := hn; omega) with rfl | hn3
  · exact absurd hJ (ggD4InnerOneInput_holds K (by rw [hK, pow_one]) s hs3 (Or.inl hd) J)
  obtain rfl := eq_centDer_of_isComponentOf hK hn hn3 hs3 hd hJ
  obtain ⟨E, _, _, hE, ⟨e⟩⟩ := exists_centDer_mulEquiv_statedSU hK hn hn3 hs3 hd
  exact largeEvenMarking_mono
    (fun _ _ _ _ _ _ h => ⟨h.1, h.2.1, center_centDer_ne_bot hK hn hn3 hs3 hd⟩)
    (largeEvenMarking_twA2_of_mulEquiv hn3 hn hE e)

end D4Inner

end CFSG.StandardType

end
