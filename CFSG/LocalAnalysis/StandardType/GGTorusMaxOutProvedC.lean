module

public import CFSG.LocalAnalysis.StandardType.GGTorusMaxSieveDefs
import CFSG.LocalAnalysis.StandardType.GGSporKOrdBMOut

public section

namespace CFSG.StandardType.FrameRoute

theorem tmOut_C (d : TauCeti.ValidLieTypeIndex) (n : ℕ) (q : TauCeti.PrimePower) (hd : d.1 = .C n q)
    (J : Type) [Group J] [Finite J] (e : Nonempty (J ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    Nat.card (MulAut J) ∣ Nat.card J * tmLieOut d.1 := by
  obtain ⟨d', hv⟩ := d
  dsimp only at hd
  subst d'
  obtain ⟨e⟩ := e
  have hn : 3 ≤ n :=
    ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1).1
  have hmodel := CFSG.Models.lieModel_C n q hv e
  have hT : CFSG.Open.StatedClassicalModel J .PSp n q.p q.exponent := by
    rcases hmodel.2 with h | ⟨h0, -⟩
    · exact h
    · exact absurd h0 (by omega)
  obtain ⟨K, hfield, hfinite, hcard, ⟨e'⟩⟩ := hT.2
  let : Field K := hfield
  let : Finite K := hfinite
  have hout := (CFSG.RankThree.Classical.higher_symplectic_outer_order_divides_field_multiplier_bound
    q.prime_p q.exponent_pos hn hcard).1
  have houtJ : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer J) ∣
      q.exponent * Nat.gcd 2 (q.p ^ q.exponent - 1) := by
    rw [Nat.card_congr
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv]
    exact hout
  have haut : Nat.card (MulAut J) ∣
      Nat.card J * (q.exponent * Nat.gcd 2 (q.p ^ q.exponent - 1)) :=
    CFSG.StandardType.SporadicShape.bmOut_card_aut_dvd houtJ
  have htmLie : tmLieOut (.C n q) = q.exponent * Nat.gcd 2 (q.p ^ q.exponent - 1) := by
    show Nat.gcd 2 (q.card - 1) * q.exponent = q.exponent * Nat.gcd 2 (q.p ^ q.exponent - 1)
    rw [TauCeti.PrimePower.card_def, Nat.mul_comm]
  rw [htmLie]
  exact haut

end CFSG.StandardType.FrameRoute

end
