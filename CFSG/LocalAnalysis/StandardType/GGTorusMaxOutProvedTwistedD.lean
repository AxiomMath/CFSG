module

public import CFSG.LocalAnalysis.StandardType.GGTorusMaxSieveDefs
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalMinusOuterOrder
import CFSG.LocalAnalysis.StandardType.GGSporKOrdBMOut

public section

namespace CFSG.StandardType.FrameRoute

theorem tmOut_twistedD (d : TauCeti.ValidLieTypeIndex) (n : ℕ) (q : TauCeti.PrimePower)
    (hd : d.1 = .twistedD n q)
    (J : Type) [Group J] [Finite J]
    (e : Nonempty (J ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    Nat.card (MulAut J) ∣ Nat.card J * tmLieOut d.1 := by
  obtain ⟨d', hv⟩ := d
  have hd' : d' = .twistedD n q := hd
  subst hd'
  obtain ⟨e⟩ := e
  have hm : CFSG.Models.LieModel J .POmegaMinus n q.p q.exponent :=
    CFSG.Models.lieModel_twistedD n q hv e
  have hn : n ≠ 0 := by
    obtain ⟨-, -, hn4⟩ := hm.1
    omega
  have hT : CFSG.Open.StatedClassicalModel J .POmegaMinus n q.p q.exponent :=
    CFSG.Models.LieModel.statedClassicalModel_of_ne_zero hn hm
  have hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer J) ∣
      Nat.gcd 4 (q.card ^ n + 1) * q.exponent * 2 := by
    have h :=
      CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter.card_outer_dvd_of_pOmegaMinus
        (T := J) hT
    simpa only [TauCeti.PrimePower.card_def] using h
  simpa only [tmLieOut] using
    CFSG.StandardType.SporadicShape.bmOut_card_aut_dvd hout

end CFSG.StandardType.FrameRoute

end
