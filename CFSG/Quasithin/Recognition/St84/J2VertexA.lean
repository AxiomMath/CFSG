module

public import CFSG.Quasithin.Recognition.St84.J2LocalData
public import CFSG.Quasithin.Recognition.J2RecCzIso

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G]

theorem J2LocalData.nonempty_mulEquiv_model [Finite G] {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) (hD : J2LocalData L1 L2 S) :
    Nonempty (↥(L2 ⊔ bigB L2 L1 S) ≃* J2Cz.Model) := by
  have hsup : L2 ⊔ bigB L2 L1 S = L2 := hD.sup_eq
  have hchar : CharTwo (L2 ⊔ bigB L2 L1 S) :=
    F1.parabolic_charTwo (hyp111R_of_vs3_va5 hF h1 h2).symm
  rw [hsup] at hchar ⊢
  obtain ⟨K, hKL2, hKQ, hK⟩ := hD.split_right
  exact CFSG.Quasithin.nonempty_mulEquiv_model_of_complement (P := L2) (K := K)
    hD.q8d8_right.nonempty_mulEquiv_QM hchar (J2LocalData.card_right h2 hD) hKL2 hKQ hK

end CFSG.Quasithin.F112R.St84
