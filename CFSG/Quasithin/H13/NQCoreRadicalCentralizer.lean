module

public import CFSG.Quasithin.H13.NQSetupDefs

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup CFSG.Open

@[expose] def StmtSNRadicalCentralizer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T D : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → quasithinIsFaithfulLocal T D → T ≤ normalizer (D : Set G) →
    ¬ CFSG.IsQuasisimple (↥D ⧸ CFSG.pCore 2 ↥D) →
    D ⊓ centralizer (qtnqVc (normalizer (D : Set G)) : Set G) =
      (CFSG.solvableRadical ↥D).map D.subtype

end CFSG.Quasithin.H13.NQCore
