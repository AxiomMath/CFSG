module

public import CFSG.LocalAnalysis.StandardType.GGTorusMaxSieveDefs
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalPlusOuterOrder
import CFSG.LocalAnalysis.StandardType.GGSporKOrdBMOut

public section

namespace CFSG.StandardType.FrameRoute

theorem tmOut_D (d : TauCeti.ValidLieTypeIndex) (n : ℕ) (q : TauCeti.PrimePower)
    (hd : d.1 = .D n q)
    (J : Type) [Group J] [Finite J] (e : Nonempty (J ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    Nat.card (MulAut J) ∣ Nat.card J * tmLieOut d.1 := by
  obtain ⟨d', hv⟩ := d
  subst hd
  obtain ⟨e⟩ := e
  have hn : n ≠ 0 := by
    have hr := (TauCeti.LieTypeIndex.inStandardRange_iff _).mp
      ((TauCeti.LieTypeIndex.valid_iff _).mp hv).1
    omega
  have hmodel := CFSG.Models.lieModel_D n q hv e
  have hb : CFSG.Blueprint.LieModel J .POmegaPlus n q.p q.exponent :=
    CFSG.Models.LieModel.toBlueprint (by decide) hmodel
  have hT : CFSG.Open.StatedClassicalModel J .POmegaPlus n q.p q.exponent :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero hn hb
  have hout :=
    CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter.card_outer_dvd_of_pOmegaPlus J hT
  have ht : tmLieOut (.D n q) = Nat.gcd 4 (q.card ^ n - 1) * q.exponent *
      (if n = 4 then 6 else 2) := by
    rw [tmLieOut.eq_5]
  rw [ht, TauCeti.PrimePower.card_def]
  exact CFSG.StandardType.SporadicShape.bmOut_card_aut_dvd hout

end CFSG.StandardType.FrameRoute

end
