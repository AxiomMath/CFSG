module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedDefs
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank

section Genuine

@[expose] def GGA6F4ClassInput
    : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    ∀ (G : Type) [Group G] [Finite G]
      (_ : G ≃* ↥(CFSG.Blueprint.Chevalley.adjointGroup .F4 K)) (p : ℕ), p.Prime → p ≠ 2 →
      ∀ x : G, orderOf x = p → x ≠ 1 →
      ∀ D J L : Subgroup G, IsElemAbelian p D → Nat.card D = p ^ 2 → x ∈ D →
        J ≤ Subgroup.centralizer ({x} : Set G) →
        IsComponentOf L (Subgroup.centralizer ({x} : Set G)) → J ≤ L →
        Nonempty (↥J ≃* alternatingGroup (Fin 6)) → D ≤ Subgroup.centralizer (J : Set G) →
        ¬ D ≤ Subgroup.centralizer (L : Set G) →
        p = 3 ∧ Nonempty (↥L ≃* CFSG.SeitzReduction.F4Pilot.C3Levi K)

end Genuine

end CFSG.StandardType.A6Red
