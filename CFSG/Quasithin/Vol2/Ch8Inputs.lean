module

public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Quasithin.Background.HDefs
public import CFSG.Quasithin.H13.StatementsCh7

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H

variable {G : Type} [Group G]

@[expose] def LeFixI {V : Subgroup G} (hV : IsElemAbelian 2 V) (U : Subgroup G)
    (X : Subgroup (MulAut (IntMod V hV))) : Prop :=
  ∀ v : IntMod V hV, v.val ∈ U → ∀ x ∈ X, x v = v

@[expose] def Input8_1_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    fsuM T L ≤ Subgroup.normalizer (L : Set G) → ∀ hV : IsElemAbelian 2 (fsuV T I),
    ∀ U : Subgroup G, U ≤ fsuV T I → U ≠ ⊥ → ¬ Subgroup.centralizer (U : Set G) ≤ fsuM T L →
      (∃ A : Subgroup (MulAut (IntMod (fsuV T I) hV)), IsFOneOffender (autI hV ⊤) A ∧
          LeFixI hV U A) ∨
        (∃ y ∈ autI hV ⊤, y ≠ 1 ∧ Odd (orderOf y) ∧ LeFixI hV U (Subgroup.zpowers y))

end CFSG.Quasithin.H13
