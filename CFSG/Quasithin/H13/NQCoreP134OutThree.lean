module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.QuasithinUnique.Vol2Native

@[expose] def OutThreeFact : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A), SQTKHypCat A → L.Normal →
    CFSG.IsComponent L →
    ∃ D : Subgroup A, D.Normal ∧ L ⊔ Subgroup.centralizer (L : Set A) ≤ D ∧
      (∀ U : Subgroup A, IsPGroup 3 U → ∃ u ∈ U, U ≤ Subgroup.zpowers u ⊔ D) ∧
      (∀ U : Subgroup A, U ≤ D → IsPGroup 3 U →
        ∃ u ∈ U, U ≤ Subgroup.zpowers u ⊔ (L ⊔ Subgroup.centralizer (L : Set A)))

end CFSG.Quasithin.H13.NQCore
