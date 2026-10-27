module

public import CFSG.Quasithin.Background.RonanE43Central
public import CFSG.Quasithin.Background.RonanE43Out
public import CFSG.Quasithin.Background.RonanE43M24Lat

public section

namespace CFSG.Quasithin.RonanE43

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3


theorem e43_M24 (G : Type) [Group G] [Finite G] (V : Type) [CommGroup V] [Finite V]
    (ρ : G →* MulAut V) (hρ : Function.Injective ρ) (hO2 : pCoreOf 2 (⊤ : Subgroup G) = ⊥)
    (T L : Subgroup G) (hT : IsSylowIn 2 T ⊤) (hlt : fixV ρ.range < fixV (T.map ρ))
    (hLF : L = CFSG.generalizedFitting G) (hLq : CFSG.IsQuasisimple ↥L)
    (h : IsSporadic .M24 (↥L ⧸ Subgroup.center ↥L)) : aParam ρ.range ≤ 3 := by
  have hind : L.index = 1 := index_eq_one_of_M24 hLF hLq h
  have hLtop : L = ⊤ := Subgroup.index_eq_one.mp hind
  have hLT : L ⊔ T = ⊤ := by rw [hLtop]; exact top_sup_eq T
  obtain ⟨e⟩ := h
  have e' : (↥L ⧸ Subgroup.center ↥L) ≃* ↥CFSG.Blueprint.NativeSporadic.M24 := e
  obtain ⟨π, hπ, hker, hodd⟩ := exists_central_hom hLtop e' hO2
  obtain ⟨F, hFc, hFne, hSF, h2F, hgen⟩ := m24_family
  have := aParam_le_of_central_family V ρ hρ hO2 hT hLF hLq hLT hlt π hπ hker hodd
    m24_isSylowIn F hFne hSF h2F hgen
  exact this.trans hFc

end CFSG.Quasithin.RonanE43
