module

public import CFSG.LocalAnalysis.StandardType.GGTorusMaxSieveDefs
public import CFSG.LieType.Chevalley.TwistedE6OuterOrder
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate122
public import Certificates.Certificate123
import CFSG.Adapters.TauCetiExceptional.EvenB1
import CFSG.Adapters.TauCetiExceptional.B1Exceptional
import CFSG.LieType.Chevalley.TwistedE6NormalForm
import CFSG.LocalAnalysis.StandardType.GGSporKOrdBMOut
import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem tmOut_twistedE6
    (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower)
    (hd : d.1 = .twistedE6 q)
    (J : Type) [Group J] [Finite J] (e : Nonempty (J ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    Nat.card (MulAut J) ∣ Nat.card J * tmLieOut d.1 := by
  obtain ⟨d', hv⟩ := d
  have hd' : d' = .twistedE6 q := hd
  subst hd'
  obtain ⟨e⟩ := e
  have hm : CFSG.Blueprint.ChevalleyExceptionalModel J .twistedE6 q.p q.exponent := by
    refine ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, ?_⟩
    by_cases hp2 : q.p = 2
    · exact CFSG.TauCetiBridge.Even.twistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.twistedBridgeEven_twistedE6 q hv hp2 (by decide) e
    · exact CFSG.TauCetiBridge.twistedModel_of_bridge
        CFSG.TauCetiBridge.Twisted.twistedBridge_twistedE6 q hv hp2 (by decide) e
  obtain ⟨K, hField, hFinite, σ, hK, hσ, ⟨e2⟩⟩ :=
    CFSG.LieType.Chevalley.exists_mulEquiv_graphFixedRootGroup_E6 hm
  let : Field K := hField
  let : Finite K := hFinite
  have h1 := CFSG.LieType.Chevalley.card_outer_twistedE6RootGroup_dvd
    q.prime_p q.exponent_pos K hK σ hσ
  have hOutJ : Nat.card (Outer J) ∣ 2 * Nat.gcd 3 (q.card + 1) * q.exponent := by
    have h1' : Nat.card (Outer (CFSG.LieType.Chevalley.twistedE6RootGroup K σ)) ∣
        2 * Nat.gcd 3 (q.card + 1) * q.exponent := by
      simpa only [TauCeti.PrimePower.card_def] using h1
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e2).toEquiv]
    exact h1'
  refine CFSG.StandardType.SporadicShape.bmOut_card_aut_dvd ?_
  simpa only [tmLieOut, TauCeti.PrimePower.card_def] using hOutJ

end CFSG.StandardType.FrameRoute

end
