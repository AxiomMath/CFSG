module

public import CFSG.Quasithin.H13.KGLieNat

public section

namespace CFSG.Quasithin.H13.KGLie

open CFSG.Open CFSG.Quasithin Subgroup CFSG.Assembly.LowTwoRank

theorem factLieSU3Row1321_holds : A5.FactLieSU3Row1321 := by
  intro V _ _ hV2 G L v hB4 hc m hm h
  obtain ⟨K, _, _, hK, hr⟩ := h
  have h8 : 8 ≤ Nat.card K := by
    rw [hK, ← pow_mul]
    exact eight_le_two_pow (by omega)
  exact false_of_nat hV2 hB4 hc (ι := Fin 3) (by simp) h8 hr

theorem factLieSzRow1321_holds : A5.FactLieSzRow1321 := by
  intro V _ _ hV2 G L v hB4 hc f h
  obtain ⟨a, ha, rfl, K, _, _, hK, hr⟩ := h
  exact false_of_nat hV2 hB4 hc (ι := Fin 4) (by simp) (hK ▸ eight_le_two_pow (by omega)) hr

end CFSG.Quasithin.H13.KGLie
