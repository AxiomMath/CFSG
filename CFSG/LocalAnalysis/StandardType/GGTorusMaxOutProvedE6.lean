module

public import CFSG.LocalAnalysis.StandardType.GGTorusMaxSieveDefs
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
public import Certificates.Certificate3951
import CFSG.LieType.Chevalley.E6OuterOrder
import CFSG.LieType.SeitzGeneration.ExcPlaneModel
import CFSG.Adapters.TauCetiExceptional.EvenAll
import CFSG.LocalAnalysis.StandardType.GGSporKOrdBMOut
import CFSG.Models.Blueprint
public import CFSG.LieType.Chevalley.RootCommutatorData

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Blueprint.Chevalley

theorem tmOut_E6
    (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower) (hd : d.1 = .E6 q)
    (J : Type) [Group J] [Finite J] (e : Nonempty (J ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    Nat.card (MulAut J) ∣ Nat.card J * tmLieOut d.1 := by
  obtain ⟨d', hv⟩ := d
  dsimp only at hd
  subst hd
  obtain ⟨e⟩ := e
  obtain ⟨K, _, _, hK, -, ⟨φ⟩⟩ :=
    CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
      CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
  let e' : J ≃* adjointGroup .E6 K := e.trans φ
  have hK' : Nat.card K = q.p ^ q.exponent := by
    rw [TauCeti.PrimePower.card_def] at hK
    exact hK
  have hOutK : Nat.card (Outer (adjointGroup .E6 K)) ∣
      2 * Nat.gcd 3 (q.p ^ q.exponent - 1) * q.exponent :=
    CFSG.LieType.Chevalley.card_outer_adjointGroup_E6_dvd
      q.prime_p q.exponent_pos K hK'
  have hOutJ : Nat.card (Outer J) ∣
      2 * Nat.gcd 3 (q.p ^ q.exponent - 1) * q.exponent := by
    rw [Nat.card_congr
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e').toEquiv]
    exact hOutK
  have haut := CFSG.StandardType.SporadicShape.bmOut_card_aut_dvd hOutJ
  have htm : tmLieOut (.E6 q) = 2 * Nat.gcd 3 (q.p ^ q.exponent - 1) * q.exponent := by
    simp only [tmLieOut, TauCeti.PrimePower.card_def]
  change Nat.card (MulAut J) ∣ Nat.card J * tmLieOut (.E6 q)
  rw [htm]
  exact haut

end CFSG.StandardType.FrameRoute

end
