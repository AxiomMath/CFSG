module

public import CFSG.Quasithin.Vol2.Ch11SecOE8J
public import CFSG.Quasithin.Vol2.Ch11SecOE9F
public import CFSG.Quasithin.Vol2.Ch11SecOE7J
public import CFSG.Quasithin.Vol2.Ch11SecOE8I

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

open CFSG.Open CFSG.Quasithin
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {G : Type} [Group G] [Finite G]

theorem nParam_le_of_isPSL3_of_untwisted {T : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (hL : IsPSL 3 2 n ↥(CFSG.generalizedFitting G)) (hT : quasithinIsSylowTwo T)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤)
    (hun : ¬ E2.IsDiagramNontrivial T (CFSG.generalizedFitting G)
      (T ⊓ CFSG.generalizedFitting G)) :
    E1.nParam (⊤ : Subgroup G) ≤ n := by
  obtain ⟨⟨-, hn1, -⟩, K, _, _, hK, ⟨e⟩⟩ := hL
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hn1 hK
  have : (CFSG.generalizedFitting G).Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := G)).2
  have hT' : IsSylowIn 2 T ⊤ := ⟨le_top, hT.1, by rw [Subgroup.relIndex_top_right]; exact hT.2⟩
  exact nParam_le_of_psl3_of_untwisted hT' hFT hn hK
    (e.trans (QuasithinUnique.Setup.X7a.statedSLEquivProjectiveSL 3 K)) hun

@[expose] def E114TwistedUpper : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), SQTKGroup G →
    IsSimpleGroup (ASInputs.FStar G) → quasithinIsSylowTwo T →
    CFSG.generalizedFitting G ⊔ T = ⊤ → ∀ n : ℕ, 2 ≤ n →
      (IsPSL 3 2 n (ASInputs.FStar G) ∨ IsPSp4 2 n (ASInputs.FStar G)) →
      E2.IsDiagramNontrivial T (CFSG.generalizedFitting G) (T ⊓ CFSG.generalizedFitting G) →
        E1.nParam (⊤ : Subgroup G) ≤ n

theorem e114LieL3Sp4_of_twistedUpper (h : E114TwistedUpper) : E114LieL3Sp4 := by
  intro G _ _ T hSQ hFs hT hFT n hn hty
  have hup : E1.nParam (⊤ : Subgroup G) ≤ n := by
    by_cases htw : E2.IsDiagramNontrivial T (CFSG.generalizedFitting G)
        (T ⊓ CFSG.generalizedFitting G)
    · exact h G T hSQ hFs hT hFT n hn hty htw
    · rcases hty with hL | hS
      · exact nParam_le_of_isPSL3_of_untwisted hn hL hT hFT htw
      · exact nParam_le_of_isPSp4_of_untwisted hS hT hFT htw
  refine le_antisymm hup ?_
  rcases hty with hL | hS
  · exact le_nParam_of_isPSL3 hn hL hFs hT hFT
  · exact le_nParam_of_isPSp4 hS hFs hT hFT

theorem e114LieCited_of_twistedUpper (h : E114TwistedUpper) : SecE3.E114LieCited :=
  e114LieCited_of_L3Sp4 (e114LieL3Sp4_of_twistedUpper h)

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
