module

public import CFSG.LocalAnalysis.StandardType.GGTorusMaxSieveDefs
import CFSG.LocalAnalysis.StandardType.GGSporKOrdBMOut

public section

namespace CFSG.StandardType.FrameRoute

theorem tmOut_B_even (d : TauCeti.ValidLieTypeIndex) (n : ℕ) (q : TauCeti.PrimePower)
    (hd : d.1 = .B n q) (hn : 3 ≤ n) (hp : q.p = 2)
    (J : Type) [Group J] [Finite J] (e : Nonempty (J ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    Nat.card (MulAut J) ∣ Nat.card J * tmLieOut d.1 := by
  obtain ⟨d', hv⟩ := d
  subst hd
  obtain ⟨e⟩ := e
  rcases CFSG.Models.lieModel_B n q hv e with h | h
  · have hT : CFSG.Open.StatedClassicalModel J .PSp n q.p q.exponent :=
      CFSG.Models.LieModel.statedClassicalModel_of_ne_zero (by omega) h
    obtain ⟨K, hfield, hfinite, hcard, ⟨e'⟩⟩ := hT.2
    let hF : Field K := hfield
    let hFin : Finite K := hfinite
    have hout := (CFSG.RankThree.Classical.higher_symplectic_outer_order_divides_field_multiplier_bound
      q.prime_p q.exponent_pos hn hcard).1
    have houtR : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer J) ∣
        q.exponent * Nat.gcd 2 (q.p ^ q.exponent - 1) := by
      rw [Nat.card_congr
        (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv]
      exact hout
    have hn2 : ¬ (n = 2 ∧ q.p = 2) := by omega
    have ht : tmLieOut (.B n q) = q.exponent * Nat.gcd 2 (q.p ^ q.exponent - 1) := by
      rw [tmLieOut.eq_3, if_neg hn2]
      simp only [TauCeti.PrimePower.card_def, Nat.mul_one]
      ring
    rw [ht]
    exact CFSG.StandardType.SporadicShape.bmOut_card_aut_dvd houtR
  · exact absurd hp h.1.2.2.2

end CFSG.StandardType.FrameRoute

end
