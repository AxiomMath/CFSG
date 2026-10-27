module

public import CFSG.LocalAnalysis.StandardType.GGTorusMaxSieveDefs
import CFSG.Adapters.LieModelL4U4Sp4Torus
import CFSG.LocalAnalysis.StandardType.GGSporKOrdBMOut

public section

namespace CFSG.StandardType.FrameRoute

theorem tmOut_B_two_even (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower)
    (hd : d.1 = .B 2 q) (hp : q.p = 2)
    (J : Type) [Group J] [Finite J] (e : Nonempty (J ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    Nat.card (MulAut J) ∣ Nat.card J * tmLieOut d.1 := by
  obtain ⟨d', hv⟩ := d
  subst hd
  obtain ⟨e⟩ := e
  have hodd : Odd (2 ^ q.exponent - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow
      (Nat.even_pow.mpr ⟨even_two, by have := q.exponent_pos; omega⟩) odd_one
  have hg : Nat.gcd 2 (2 ^ q.exponent - 1) = 1 := Nat.coprime_two_left.mpr hodd
  rcases CFSG.Models.lieModel_B 2 q hv e with h | h
  · have hb : CFSG.Blueprint.LieModel J .PSp 2 q.p q.exponent :=
      CFSG.Models.LieModel.toBlueprint (by decide) h
    have hout : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer J) ∣
        2 * q.exponent := by
      have h0 := CFSG.Blueprint.LieModel.card_outer_psp4_dvd hb
      rw [hp] at h0
      simpa [hg] using h0
    have ht : tmLieOut (.B 2 q) = 2 * q.exponent := by
      rw [tmLieOut.eq_3, if_pos ⟨rfl, hp⟩, TauCeti.PrimePower.card_def, hp, hg]
      ring
    rw [ht]
    exact CFSG.StandardType.SporadicShape.bmOut_card_aut_dvd hout
  · exact absurd hp h.1.2.2.2

end CFSG.StandardType.FrameRoute

end
