module

public import CFSG.Quasithin.Vol2.Ch11SecBDerived35
public import CFSG.Quasithin.Vol2.Ch11L2Q5cMult

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

theorem inputSchurSL2_of (hI13 : SecH.AS_I_1_3_L2) : InputSchurSL2 := by
  intro k hk F _ _ hF X _ _ φ hφ hX hO2 hker
  have hP : Group.IsPerfect X := ⟨hX⟩
  rcases hI13 k hk F hF X hP φ.ker hker
      ⟨QuotientGroup.quotientKerEquivOfSurjective φ hφ⟩ with h1 | ⟨-, h2, -⟩
  · exact (MonoidHom.ker_eq_bot_iff φ).mp h1
  · exfalso
    have hP2 : IsPGroup 2 φ.ker := IsPGroup.of_card (n := 1) (by rw [h2]; norm_num)
    have hle : φ.ker ≤ CFSG.pCore 2 X :=
      le_sSup (show φ.ker ∈ {K : Subgroup X | K.Normal ∧ IsPGroup 2 K} from
        ⟨inferInstance, hP2⟩)
    rw [hO2, le_bot_iff] at hle
    rw [hle, Subgroup.card_bot] at h2
    norm_num at h2

theorem inputSchurSL2_holds : InputSchurSL2 := inputSchurSL2_of SecH.as_I_1_3_L2_holds

end CFSG.Quasithin.Vol2.Ch11.SecB
