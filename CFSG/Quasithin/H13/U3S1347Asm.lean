module

public import CFSG.Quasithin.H13.U3S1347St
public import CFSG.Quasithin.H13.U3S1347Z6
public import CFSG.Quasithin.H13.U3S13473H
public import CFSG.Quasithin.H13.U3S1347P4G

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique

theorem stmt13_4_7One_of (hedge : GoldschmidtEdgeBoundS3) (h1332 : Stmt13_3_2)
    (h1228 : Stmt12_2_8) (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56)
    (h135 : A6.Stmt13_3_5) (h1345 : NQS134.Stmt13_4_5) (hF : F6.TheoremF618Cat)
    (hBig : A5.FactF618Big) : Stmt13_4_7One := fun _ _ _ _ _ _ S _ _ h =>
  s1347_one hedge h1332 h1228 hC58 h317 h56 h135 h1345 hF hBig S h

theorem stmt13_4_7L2_of (hC137 : C137StatementFiveZ)
    (hedge : GoldschmidtEdgeBoundS3) (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8)
    (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56) (h135 : A6.Stmt13_3_5)
    (h1345 : NQS134.Stmt13_4_5) (hF : F6.TheoremF618Cat) (hBig : A5.FactF618Big)
    (h1222 : Stmt12_2_2) (h139 : A6.Stmt13_3_9) (hns : Stmt13473NonSolv)
    (htwo : ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G)
      (S : A6.Setting134 G T L V) (H₁ H₂ : Subgroup G), Hyp1347 T H₁ H₂ →
      oTwoRes H₂ = l2Of S → Concl1347ii T H₁ H₂ → ∀ X : Subgroup G, InH (H₁ ⊔ H₂) X →
        X ⊓ centralizer (quasithinOmegaOneCenter T : Set G) = T → X = H₁ ⊔ H₂) :
    Stmt13_4_7L2 := by
  intro G _ _ T L V S H₁ H₂ h hK₂L
  have h4 := s1347_four hC137 hedge h1332 h1228 hC58 h317 h56 h135 h1345 hF hBig S h hK₂L
  exact ⟨s1347_one hedge h1332 h1228 hC58 h317 h56 h135 h1345 hF hBig S h,
    htwo G T L V S H₁ H₂ h hK₂L,
    s1347_three hns hF hBig hedge h1332 h1228 hC58 h317 h56 h135 h1222 h139 S h hK₂L, h4.1, h4.2⟩

end CFSG.Quasithin.H13.U3
