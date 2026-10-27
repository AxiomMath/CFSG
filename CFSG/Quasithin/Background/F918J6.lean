module

public import CFSG.Quasithin.Background.F918J1
public import CFSG.Quasithin.Background.F918J2
public import CFSG.Quasithin.Background.F918J3
public import CFSG.Quasithin.Background.F918J4
public import CFSG.Quasithin.Background.F918J5

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

theorem insp5a_of_inputs
    (hA21 : AsA21SQTKSection) (h45 : AsB45) (hF : Vol2.Ch10.SecA.Facts10_1)
    (hX : Insp5aNonShape) : Insp5a := by
  intro W _ _ M Mp T L V t hD _ htT htL hMp hV0 hcomm hq hL38
  have hN := insp5a_normalizes hD htT htL hMp hV0 hcomm hL38
  have hQ := insp5a_qsec hD htT htL hMp hV0 hcomm hL38 hN
  have hS := insp5a_sqtk hA21 hD hcomm hL38
  have hLV : L ≤ stabSub V := insp5a_le_stabSub hD
  have hfaith : L ⊓ centSub V = ⊥ := insp5a_faithful hD hcomm hL38
  obtain ⟨e⟩ := insp5a_equiv hD hcomm hL38
  have hsimp : IsSimpleGroup ↥L :=
    CFSG.QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types hL38
  have : IsSimpleGroup ↥(autSub L V) := e.symm.isSimpleGroup
  have hAK : A38Types ↥(autSub L V) := a38Types_congr e hL38
  have hexp : ∀ u : ↥V, u ^ 2 = 1 := fun u => Subtype.ext (hD.exp u)
  obtain ⟨hshape, hmods⟩ := insp5a_rows h45 hF hX hexp hQ hS hq hAK
  have hLMp : L ≤ Mp := hMp ▸ le_sup_left
  have hLZ : L ≤ stabSub (V ⊓ fixV Mp) :=
    le_stabSub_of_le_fixV (inf_le_right.trans (fixV_anti hLMp))
  have hZV : V ⊓ fixV Mp ≤ V := inf_le_left
  refine ⟨fiveShape_of_isShapeGroup (hshape.of_mulEquiv e), hcomm, ?_⟩
  rcases hmods with (⟨n, -, h⟩ | h | h) | (⟨m, hm, h⟩ | ⟨f, h⟩)
  · exact Or.inl ⟨n, binaryNaturalSL_of_autSub hLV hLZ hZV hfaith h⟩
  · exact Or.inr (Or.inl (binaryNaturalSL_of_autSub hLV hLZ hZV hfaith h))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (alternatingNatural_of_autSub hLV hLZ hZV hfaith h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨m, hm, binaryOrthogonalFour_of_autSub hLV hLZ hZV hfaith h⟩)))
  · exact Or.inr (Or.inr (Or.inl ⟨f, binaryNaturalSz_of_autSub hLV hLZ hZV hfaith h⟩))

end CFSG.Quasithin
