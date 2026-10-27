module

public import CFSG.Quasithin.Vol2.Ch11SecOE8K
public import CFSG.Quasithin.Vol2.Ch11SecOE8V

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

open CFSG.Open CFSG.Quasithin

@[expose] def E114TwistedUpperSp4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), SQTKGroup G →
    IsSimpleGroup (ASInputs.FStar G) → quasithinIsSylowTwo T →
    CFSG.generalizedFitting G ⊔ T = ⊤ → ∀ n : ℕ, 2 ≤ n → IsPSp4 2 n (ASInputs.FStar G) →
      E2.IsDiagramNontrivial T (CFSG.generalizedFitting G) (T ⊓ CFSG.generalizedFitting G) →
        E1.nParam (⊤ : Subgroup G) ≤ n

theorem e114TwistedUpper_of_sp4 (h : E114TwistedUpperSp4) : E114TwistedUpper := by
  intro G _ _ T hSQ hFs hT hFT n hn hty htw
  rcases hty with hL | hS
  · exact nParam_le_of_isPSL3_of_twisted hn hL hFs hT hFT htw
  · exact h G T hSQ hFs hT hFT n hn hS htw

theorem e114LieCited_of_twistedUpperSp4 (h : E114TwistedUpperSp4) : SecE3.E114LieCited :=
  e114LieCited_of_twistedUpper (e114TwistedUpper_of_sp4 h)

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
