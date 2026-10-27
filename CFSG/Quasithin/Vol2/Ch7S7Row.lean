module

public import CFSG.Quasithin.Background.HA7Row
public import CFSG.Quasithin.Vol2.Ch7NotFF

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

@[expose] def Stmt7_2_1_S7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G),
    ∀ hV : IsElemAbelian 2 (fsuV T I), fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) →
      Subgroup.normalizer (fsuV T I : Set G) ≤ fsuM T L → ∀ _ : IsMulCommutative ↥(fsuV T I),
      Row711S7Pair T L I →
        aParam (autI hV ⊤) ≤ 2 ∧ 4 ≤ mParam (autI hV ⊤) ∧ CFSG.Open.pRank 2 (autI hV ⊤) ≤ 3 ∧
          (4 : ℕ∞) ≤ betaH (autI hV ⊤) ∧ alphaH (autI hV ⊤) = 1

theorem stmt7_2_1_S7
    : Stmt7_2_1_S7 := by
  intro G _ _ T L I hV hN hNM _ hrow
  obtain ⟨htw, hnat⟩ := hrow
  obtain ⟨φ, hφN, hinf, hsup, hniso⟩ := exists_twist hV hN hNM htw
  have hL : A7Four (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) (intSub hV I) ⊥ := hnat
  exact A7.H8_A7Pair_params hL hφN hinf hsup hniso (autI_top_le_normalizer hV hNM)

end CFSG.Quasithin.H13
