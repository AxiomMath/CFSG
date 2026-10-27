module

public import CFSG.Quasithin.Background.RonanE114D4Model
public import CFSG.Quasithin.Background.A3StructureDefs

public section

namespace CFSG.Quasithin.RonanE114

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b _root_.Certificates

section

theorem clause_two_le {G : Type} [Group G] [Finite G] {T : Subgroup G} (hT : IsSylowIn 2 T ⊤)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) {n : ℕ} (hn : 1 ≤ n)
    (hL : Is3D4 2 n ↥(CFSG.generalizedFitting G)) :
    E1.nParam (⊤ : Subgroup G) ≤ ((3 * n : ℕ) : ℕ∞) := by
  haveI : (CFSG.generalizedFitting G).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := G)).2
  exact nParam_le_three_mul hT hFT hn hL

end

end CFSG.Quasithin.RonanE114
