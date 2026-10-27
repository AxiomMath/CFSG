module

public import CFSG.Quasithin.Vol2.Ch3E213MOLA6
public import CFSG.Quasithin.Vol2.Ch3E213MOLA8
public import CFSG.Quasithin.Vol2.Ch3E213MOLA9
public import CFSG.ClassicalInvolution.ModelFacts.LinearAutMain
public import CFSG.Quasithin.Vol2.Ch3E213MOLFacts

public section

namespace CFSG.Quasithin.Ch3E213M.OLA


theorem kFactL3U3OuterInv_holds : OL.KFactL3U3OuterInv := by
  intro K _ _ p hp hp5 hK S
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  rcases hK with ⟨hp4, hU⟩ | ⟨hp4, hL⟩
  · obtain ⟨F, _, _, _, hcard, θ, hθ, hker⟩ := exists_theta_uni hU
    exact uni_kfact hcard hp2 (by rw [pow_one]; exact hp5) (by rw [pow_one]; exact hp4) θ hθ
      hker S
  · obtain ⟨θ, hθ, hker⟩ := exists_theta_lin hL
    have hG : Nat.card (GaloisField p 1) = p := by rw [GaloisField.card p 1 one_ne_zero, pow_one]
    exact lin_kfact (by rw [hG]; exact hp4) (by rw [hG]; exact hp5)
      (CFSG.ClassicalInvolution.ModelFacts.LinearAut.linearAutClassification hp2
        (by rw [pow_one]; exact hp5) (le_refl 3)) θ hθ hker S

end CFSG.Quasithin.Ch3E213M.OLA
