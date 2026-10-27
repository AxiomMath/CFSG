
module

public import CFSG.Quasithin.Vol2.Ch1Quotient
public import CFSG.Quasithin.EmptyFaithful.QTKELocal
public import CFSG.Quasithin.Background.A3StructureBasic

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

@[expose] def A37ForSQTK : Prop := ∀ (Q : Type) [Group Q], SQTKHyp Q → A37Statement Q

@[expose] def A38ForSQTK : Prop := ∀ (Q : Type) [Group Q], SQTKHyp Q → A38Part3 Q

@[expose] def A39ForSQTK : Prop := ∀ (Q : Type) [Group Q], SQTKHyp Q → A39Statement Q

section QTKE

variable {G : Type} [Group G] [Finite G]

theorem sqtkGroup_of_pCoreOf_ne_bot (hK : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {H : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) : SQTKGroup ↥H :=
  ⟨stronglyQuasithin_of_pCoreOf_ne_bot hK hH, kGroup_of_pCoreOf_ne_bot hK hs hnab hH⟩

theorem sqtkHyp_quotient_of_pCoreOf_ne_bot (hK : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {H : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) :
    SQTKHyp (↥H ⧸ CFSG.pCore 2 ↥H) :=
  SQTKHyp.of_sqtkGroup ↥H (sqtkGroup_of_pCoreOf_ne_bot hK hs hnab hH)

theorem lemma_1_2_1_one (hK : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h39 : A39ForSQTK) {H : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) :
    cCompSpan H = perfectCore H :=
  cCompSpan_eq_perfectCore_of_subgroup H
    (h39 _ (sqtkHyp_quotient_of_pCoreOf_ne_bot hK hs hnab hH)).1

theorem lemma_1_2_4_exists (hK : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK) (h39 : A39ForSQTK)
    {H S B : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) (hS : IsSylowTwoOf S H) (hBH : B ≤ H)
    (hB : B ∈ lFamily S) : ∃ L ∈ cComp H, B ≤ L :=
  have hQ := sqtkHyp_quotient_of_pCoreOf_ne_bot hK hs hnab hH
  exists_cComp_ge_of_subgroup hS hBH hB (h37 _ hQ) (h39 _ hQ)

theorem normal_conjClosure_of_pCoreOf_ne_bot (hK : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    {H T L : Subgroup G} (hH : pCoreOf 2 H ≠ ⊥) (hT : IsSylowTwoOf T H) (hL : L ∈ cComp H) :
    H ≤ Subgroup.normalizer (conjClosure L T : Set G) :=
  have hQ := sqtkHyp_quotient_of_pCoreOf_ne_bot hK hs hnab hH
  normal_conjClosure_of_subgroup hT hL (h37 _ hQ) (h38 _ hQ)

end QTKE

end CFSG.Quasithin
