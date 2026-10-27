module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Quasithin.Vol2.Ch12Sec8OneHat
public import CFSG.Quasithin.Vol2.Ch12Sec9Statements

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

@[expose] def Case1294FiveID : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G), Cx1291 G T L V 4 →
    ∀ V₁ V₂ K₁ : Subgroup G, Setting1282One G T L V 4 V₁ V₂ → lOne L V₁ ≤ K₁ →
      quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)) →
      Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) →
      ∀ D : HatModelU (u128 V V₁), G112Concl5 D.B (D.img (Subgroup.normalizer (V₁ : Set G))) →
        (D.img K₁).relIndex (D.img (Subgroup.normalizer (V₁ : Set G))) ≤ 2 →
        ∃ I : Subgroup G, I ≤ zU128 V V₁ ∧ K₁ ≤ Subgroup.normalizer (I : Set G) ∧
          T ≤ Subgroup.normalizer (I : Set G) ∧ IsElemAbelian 2 I ∧ Nat.card I = 16 ∧
          K₁ ⊓ Subgroup.centralizer (I : Set G) = pCoreOf 2 K₁

end CFSG.Quasithin.H13.C1294
