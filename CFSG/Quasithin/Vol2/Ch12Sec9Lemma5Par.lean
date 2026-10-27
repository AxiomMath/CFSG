module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Quasithin.Vol2.Ch12Sec2Setting

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

@[expose] def ParabolicFact1295 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X K S B : Subgroup G), K ≤ X →
    X ≤ Subgroup.normalizer (K : Set G) → QuasithinUnique.IsSylowTwoOf S X → K ⊔ S = X →
    Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) →
    B ≤ K → S ≤ Subgroup.normalizer (B : Set G) → oTwoUpper B = B →
    Nonempty (↥B ⧸ CFSG.pCore 2 ↥B ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
    (¬ ∃ φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2),
        ((B.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K))).map φ.toMonoidHom =
          Subgroup.centralizer ({transvection15} : Set _)) →
    ∃ P : Subgroup G, S ≤ P ∧ P ≤ X ∧ (∀ Y : Subgroup G, S ≤ Y → Y ≤ P → Y = S ∨ Y = P) ∧
      (∃ y ∈ P, orderOf y = 3) ∧ P ≤ Subgroup.normalizer (B : Set G) ∧
      ⁅B, oTwoUpper P⁆ ≤ pCoreOf 2 B

end CFSG.Quasithin.H13
