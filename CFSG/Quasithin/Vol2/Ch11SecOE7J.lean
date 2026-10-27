module

public import CFSG.Quasithin.Vol2.Ch11SecOE7I
public import CFSG.Quasithin.Vol2.Ch11SecE3LieMain

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

open CFSG.Open CFSG.Quasithin

@[expose] def E114LieL3Sp4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), SQTKGroup G →
    IsSimpleGroup (ASInputs.FStar G) → quasithinIsSylowTwo T →
    CFSG.generalizedFitting G ⊔ T = ⊤ → ∀ n : ℕ, 2 ≤ n →
      (IsPSL 3 2 n (ASInputs.FStar G) ∨ IsPSp4 2 n (ASInputs.FStar G)) →
        E1.nParam (⊤ : Subgroup G) = n

theorem e114LieCited_of_L3Sp4 (h : E114LieL3Sp4) : SecE3.E114LieCited := by
  intro G _ _ T hSQ hFs hT hFT n hn hty
  rcases hty with hU | hty
  · exact nParam_eq_of_isPSU3 hU hFs hT hFT
  · exact h G T hSQ hFs hT hFT n hn hty

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
