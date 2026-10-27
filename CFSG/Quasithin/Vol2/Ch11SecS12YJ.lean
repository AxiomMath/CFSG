module

public import CFSG.Quasithin.Vol2.Ch11SecS12YI
public import CFSG.Quasithin.Vol2.Ch11SecS12V

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

@[expose] def Obl11_1_2StarSL3AbCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I V₁ V₂ X K : Subgroup G),
    StarHyp G T L I V₁ V₂ X K → KindSL3 L (fsuV T I) 2 →
    IsElemAbelian 2 (conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) ⊓
      Subgroup.centralizer (SecA.xOne X (LOf L V₁) : Set G)) →
    16 ≤ Nat.card ↥(conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) ⊓
      Subgroup.centralizer (SecA.xOne X (LOf L V₁) : Set G)) →
    (∃ y ∈ X ⊓ LOf L V₁, ∃ e ∈ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) ⊓
      Subgroup.centralizer (SecA.xOne X (LOf L V₁) : Set G), y * e * y⁻¹ ≠ e) →
      ¬ conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) ≤ pCoreOf 2 (L ⊔ T)

theorem obl11_1_2StarSL3Ab_of (hCore : Obl11_1_2StarSL3AbCore) (hC : CartanFacts)
    (hN : SecA.NatFacts) (hG2 : SecA.FactG2DerivedOrder) (hFb : SecA.Facts12b)
    (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) : Obl11_1_2StarSL3Ab := by
  intro G _ _ T L I V₁ V₂ X K h hSL3
  obtain ⟨hE, h16, hy⟩ := exists_elemAb_cU hC hN hG2 hFb h1102 h1103 h hSL3
  exact hCore G T L I V₁ V₂ X K h hSL3 hE h16 hy

theorem obl11_1_2StarSL3_of_core (hB : H13.Ch4.LemmaB414Corrected)
    (hCore : Obl11_1_2StarSL3AbCore) (hC : CartanFacts) (hN : SecA.NatFacts)
    (hG2 : SecA.FactG2DerivedOrder) (hFb : SecA.Facts12b) (h1102 : Stmt11_0_2)
    (h1103 : Stmt11_0_3) : Obl11_1_2StarSL3 :=
  obl11_1_2StarSL3_of_corrected hB (obl11_1_2StarSL3Ab_of hCore hC hN hG2 hFb h1102 h1103) hC hN
    hG2 hFb h1102 h1103

end CFSG.Quasithin.Vol2.Ch11.SecS
