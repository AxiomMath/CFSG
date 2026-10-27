module

public import CFSG.LocalAnalysis.StandardType.GGTorusMaxSieveDefs
import CFSG.LocalAnalysis.StandardType.GGSporKOrdBMOut
public import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder

public section

namespace CFSG.StandardType.FrameRoute

theorem tmOut_twistedA (d : TauCeti.ValidLieTypeIndex) (n : ℕ) (q : TauCeti.PrimePower)
    (hd : d.1 = .twistedA n q)
    (J : Type) [Group J] [Finite J] (e : Nonempty (J ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    Nat.card (MulAut J) ∣ Nat.card J * tmLieOut d.1 := by
  obtain ⟨d', hv⟩ := d
  have hd' : d' = .twistedA n q := hd
  subst hd'
  obtain ⟨e⟩ := e
  have hm : CFSG.Models.LieModel J .PSU (n + 1) q.p q.exponent := by
    have h := CFSG.Models.lieModel_twistedA n q hv e
    have hc : TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA n q, hv⟩ = q.p :=
      TauCeti.LieTypeIndex.characteristic_twistedA n q
    have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA n q, hv⟩ = q.exponent :=
      TauCeti.LieTypeIndex.fieldExponent_twistedA n q
    rwa [hc, hf] at h
  have hT : CFSG.Open.StatedClassicalModel J .PSU (n + 1) q.p q.exponent :=
    hm.2.resolve_right fun h0 => by omega
  have h2 : 2 ≤ n :=
    ((TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1).1
  have h3 : 3 ≤ n + 1 := by omega
  have hout :
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer J) ∣
        2 * Nat.gcd (n + 1) (q.card + 1) * q.exponent := by
    have h := (CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
      (Or.inr rfl) h3 q.prime_p q.exponent_pos hT).1
    simpa only [CFSG.RankThree.OuterOrder.determinantParameter, TauCeti.PrimePower.card_def,
      mul_assoc, mul_left_comm, mul_comm] using h
  simpa only [tmLieOut] using CFSG.StandardType.SporadicShape.bmOut_card_aut_dvd hout

end CFSG.StandardType.FrameRoute

end
