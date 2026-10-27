module

public import CFSG.Quasithin.EmptyFaithful.S151U7

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

@[expose] def Input15122L3WreathMinPar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L P : Subgroup G),
    Ctx15122 T Mc M Z₁ Z₂ V₁ V₂ L → Case15120TwoB T Mc Z₁ L → IsLnBlock L 3 →
    ¬ s1516 T Z₁ ≤ Subgroup.normalizer (L : Set G) →
    Par2 L (s1516 T Z₁ ⊓ Subgroup.normalizer (L : Set G)) P → ParBig L P →
    CharTwo (P ⊔ s1516 T Z₁) ∧ IsMinParabolicOf (P ⊔ s1516 T Z₁) (P ⊔ s1516 T Z₁) ∧
      ¬ C126Third (P ⊔ s1516 T Z₁) (s1516 T Z₁)

theorem input15122L3WreathStar_of_minPar (h118 : TheoremC118) (h126 : TheoremC126)
    (hm : Input15122L3WreathMinPar) : Input15122L3WreathStar := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L P hc h2B h3 hSN hpar hbig hnot
  obtain ⟨hchar, hmin, hno3⟩ := hm G T Mc M Z₁ Z₂ V₁ V₂ L P hc h2B h3 hSN hpar hbig
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hc.hL.comp
  have hHG : P ⊔ s1516 T Z₁ ≤ g1_1516 Z₁ := sup_le (hpar.le.trans hLG) (s1516_le_g1 T Z₁)
  rcases star_general h118 h126 hc le_sup_right hHG hchar hmin hno3 with h | h
  · exact le_sup_left.trans h
  · exact (hnot (le_sup_left.trans h)).elim

end CFSG.Quasithin
