module

public import CFSG.Quasithin.Background.F918X1
public import CFSG.Quasithin.Background.F918XG2aCount
public import CFSG.Quasithin.Background.F918XG2aOrd
public import CFSG.Quasithin.Background.FFC2Ident

public section

namespace CFSG.Quasithin.F918X

open CFSG.Quasithin CFSG.Open
open scoped commutatorElement

theorem case4TwistOne_holds :
    Case4TwistOne := by
  intro V _ _ _ G L hHyp hG2
  obtain ⟨-, hLn, hself, hq⟩ := FFC.b4hyp_data hHyp
  obtain ⟨K, hKf, hKfin, hKc, π, hπ⟩ := hG2
  have hK : Nat.card K = 2 := by simpa using hKc
  have hchar := FFC.charTwo_of_card_two hK
  have hinj := FFC.injective_of_zornQ_realizes hπ
  let e : ↥(quasithinG2 K) ≃* ↥(ffJ G) := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩
  have hJL : ffJ G ≠ L := by
    intro hJL
    have hperf : ⁅ffJ G, ffJ G⁆ = ffJ G := by
      rw [hJL]
      exact Subgroup.isPerfect_iff.1 hq.1
    exact commutator_ne_g2_two hK e.symm hperf
  obtain ⟨hL, hGH⟩ := FFC.ident_g2 hHyp hJL hK e.symm
  obtain ⟨hs, hnab, haut⟩ := FFC.commutator_data_g2 hK e.symm
  have hLle : L ≤ ffJ G := hL ▸ FFC.commutator_le_self_aux _
  have hLG : L < G := by
    rw [hGH]
    exact lt_of_le_of_ne hLle fun h => hJL h.symm
  subst hL
  obtain ⟨hst, hZ⟩ := stableMod_of_simple_lt hLG hLn hself hnab hs haut
  exact ⟨hst, Or.inl hZ⟩

end CFSG.Quasithin.F918X
