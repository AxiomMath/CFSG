module

public import CFSG.Quasithin.H13.GoldschmidtM22CaseBIface

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin

@[expose] def M22CaseAThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (g : G) (D : Subgroup G) (z : G),
    M22LemmasG → Hyp6Sec2 G T M L V → EndN4Concl T L V g D →
      Subgroup.centralizer (V : Set G) ≤ V → quasithinOmegaOneCenter T = Subgroup.zpowers z →
      ∃ d : G, d⁻¹ * z * d ∈ D ∧ d⁻¹ * z * d ≠ z ∧
        IsElemAbelian 2 (D ⊓ CFSG.Quasithin.conjSubgroup D d) ∧
        Nat.card ↥(D ⊓ CFSG.Quasithin.conjSubgroup D d) = 4

end CFSG.Quasithin.H13.GM22
