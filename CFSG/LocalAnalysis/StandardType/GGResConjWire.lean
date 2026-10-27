module

public import CFSG.LocalAnalysis.StandardType.GGWeylSimpleSystemsConj
public import CFSG.LocalAnalysis.StandardType.GGResLeviDatumSides
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeSides

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggResLeviDatum_of_sides_conj {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {Bs L J K : Subgroup G} (hL : GGResSideDatum p Bs L J)
    (hK : GGResSideDatum p Bs K J) : GGResLeviDatum p Bs L J K ggSelAny ggTypAny :=
  ggResLeviDatum_of_sides ggWeylSimpleSystemsConjInput_holds hp2 hL hK

theorem ggResTwoNodeDatum_of_sides_conj {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {Bs L J K : Subgroup G} (hL : GGResTwoNodeSideDatum p Bs L J)
    (hK : GGResSideDatum p Bs K J ∨ GGResTwoNodeSideDatum p Bs K J) :
    GGResTwoNodeDatum p Bs L J K ggSelAny ggTypAny :=
  ggResTwoNodeDatum_of_sides ggWeylSimpleSystemsConjInput_holds hp2 hL hK

theorem ggResModelInput_of_sides_conj
    (h : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
      ∀ [Fact p.Prime], (GGResSideDatum p Bs L J ∧ GGResSideDatum p Bs K J) ∨
        GGResRowAt ggRowNonLevi p J L ∨ GGResRowAt ggRowNonLevi p J K) :
    GGResModelInput :=
  ggResModelInput_of_sides ggWeylSimpleSystemsConjInput_holds h

theorem ggResModelInput_of_tbj_conj (hJ : GGTBJInput)
    (hX : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G) (y : G) (K : Subgroup G), GGResHyp p B Bs x L D J y K →
      ∀ [Fact p.Prime], (GGResXDatum p Bs L ∨ GGResRowAt ggRowSeven p J L) ∧
        (GGResXDatum p Bs K ∨ GGResRowAt ggRowSeven p J K)) :
    GGResModelInput :=
  ggResModelInput_of_tbj ggWeylSimpleSystemsConjInput_holds hJ hX

end CFSG.StandardType
