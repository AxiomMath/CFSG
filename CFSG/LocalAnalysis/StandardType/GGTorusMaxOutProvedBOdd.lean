module

public import CFSG.LocalAnalysis.StandardType.GGTorusMaxSieveDefs
import CFSG.LocalAnalysis.StandardType.GGSporKOrdBMOut
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalOddOuterOrder
import CFSG.RankThree.Classical.SteinbergBJOddSymplecticOuterOrder

public section

namespace CFSG.StandardType.FrameRoute

theorem tmOut_B_odd (d : TauCeti.ValidLieTypeIndex) (n : ℕ) (q : TauCeti.PrimePower)
    (hd : d.1 = .B n q) (hp : q.p ≠ 2)
    (J : Type) [Group J] [Finite J] (e : Nonempty (J ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    Nat.card (MulAut J) ∣ Nat.card J * tmLieOut d.1 := by
  obtain ⟨d', hv⟩ := d
  subst hd
  obtain ⟨e⟩ := e
  rcases CFSG.Models.lieModel_B n q hv e with h | h
  ·
    obtain ⟨-, -, hn, -⟩ := h.1
    have hT : CFSG.Open.StatedClassicalModel J .PSp n q.p q.exponent :=
      CFSG.Models.LieModel.statedClassicalModel_of_ne_zero (by omega) h
    obtain ⟨⟨-, hf, -, -⟩, K, hfield, hfinite, hK, ⟨e'⟩⟩ := hT
    let hF : Field K := hfield
    let hFin : Finite K := hfinite
    have hout :=
      (CFSG.RankThree.Classical.odd_symplectic_outer_order_divides_field_multiplier_bound
        q.prime_p hp hf hn hK).1
    have houtR : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer J) ∣
        q.exponent * Nat.gcd 2 (q.p ^ q.exponent - 1) := by
      rw [Nat.card_congr
        (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv]
      exact hout
    have ht : tmLieOut (.B n q) =
        q.exponent * Nat.gcd 2 (q.p ^ q.exponent - 1) := by
      rw [tmLieOut.eq_3, if_neg (by rintro ⟨-, h2⟩; exact hp h2),
        TauCeti.PrimePower.card_def, Nat.mul_one]
      ring
    rw [ht]
    exact CFSG.StandardType.SporadicShape.bmOut_card_aut_dvd houtR
  ·
    obtain ⟨-, -, hn, -⟩ := h.1
    have hT : CFSG.Open.StatedClassicalModel J .POmegaOdd n q.p q.exponent :=
      CFSG.Models.LieModel.statedClassicalModel_of_ne_zero (by omega) h
    have houtR : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer J) ∣
        2 * q.exponent :=
      CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter.card_outer_dvd_of_pOmegaOdd J hT
    have hqodd : Odd (q.p ^ q.exponent) := (q.prime_p.odd_of_ne_two hp).pow
    have hg : Nat.gcd 2 (q.p ^ q.exponent - 1) = 2 :=
      Nat.gcd_eq_left (even_iff_two_dvd.mp (Nat.Odd.sub_odd hqodd odd_one))
    have ht : tmLieOut (.B n q) = 2 * q.exponent := by
      rw [tmLieOut.eq_3, if_neg (by rintro ⟨-, h2⟩; exact hp h2),
        TauCeti.PrimePower.card_def, Nat.mul_one, hg]
    rw [ht]
    exact CFSG.StandardType.SporadicShape.bmOut_card_aut_dvd houtR

end CFSG.StandardType.FrameRoute

end
