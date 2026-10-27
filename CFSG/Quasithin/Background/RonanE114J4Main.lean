module

public import CFSG.Quasithin.Background.RonanE114J4Gen
public import CFSG.Quasithin.Background.RonanE114J4Hj
public import CFSG.Quasithin.Background.RonanE114J4Cent
public import CFSG.Quasithin.Background.RonanE114J4Red

public section

namespace CFSG.Quasithin.RonanE114

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Sporadic.J4

theorem nParam_J_le_two :
    E1.nParam (⊤ : Subgroup ↥J) ≤ 2 :=
  nParam_J_le_two_of_two_locals (nParam_Hj_le_one.trans (by norm_num))
    nParam_centralizer_z0_le_two

theorem clause_five_J4
    (G : Type) [Group G] [Finite G] (T : Subgroup G) (hSQ : SQTKGroup G)
    (hFs : IsSimpleGroup ↥(CFSG.generalizedFitting G)) (hT : IsSylowIn 2 T ⊤)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) :
    IsSporadic .J4 ↥(CFSG.generalizedFitting G) → E1.nParam (⊤ : Subgroup G) ≤ 2 := by
  intro hL
  have : Finite ↥J := Nat.finite_of_card_ne_zero (by rw [card_J j4Facts]; norm_num)
  obtain ⟨e⟩ := equiv_J4_of_isSylowIn hT hFT hL
  obtain ⟨e'⟩ : Nonempty (G ≃* ↥J) := ⟨e.trans (seedEquiv j4Facts.mat)⟩
  have hn := E1.Eleven.nParam_top_mulEquiv (G := G) (G' := ↥J) e'
  have hJ := nParam_J_le_two
  exact hn.trans_le hJ

end CFSG.Quasithin.RonanE114
