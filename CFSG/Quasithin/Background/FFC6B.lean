module

public import CFSG.Quasithin.Background.B5Irr

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.B5
open scoped commutatorElement

namespace B59

section Abs

variable {M : Type} [CommGroup M] [Finite M] {X K : Subgroup (MulAut M)}

theorem exists_isSylowTwoOf_ge {Ab : Subgroup (MulAut M)} (hAX : Ab ≤ X) (hA2 : IsPGroup 2 ↥Ab) :
    ∃ T : Subgroup (MulAut M), IsSylowTwoOf T X ∧ Ab ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 ↥(Ab.subgroupOf X) :=
    hA2.of_equiv (Subgroup.subgroupOfEquivOfLe hAX).symm
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  refine ⟨(Q : Subgroup ↥X).map X.subtype, ⟨Subgroup.map_subtype_le _, Q.isPGroup'.map _, ?_⟩, ?_⟩
  · have : ((Q : Subgroup ↥X).map X.subtype).subgroupOf X = (Q : Subgroup ↥X) :=
      Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
    rw [this]
    exact Q.not_dvd_index
  · intro a ha
    have : (⟨a, hAX ha⟩ : ↥X) ∈ Ab.subgroupOf X := ha
    exact ⟨⟨a, hAX ha⟩, hQ this, rfl⟩

theorem b42_offender (hB42 : AsB42) (hV : ∀ v : M, v ^ 2 = 1) (h : B51Hyp X K)
    (hU : commV K ∈ IrrPlus K ⊤) {T : Subgroup (MulAut M)} (hT : IsSylowTwoOf T X)
    {Ab : Subgroup (MulAut M)} (hAb : IsFFStarOffender X Ab) (hAbT : Ab ≤ T) {C : Subgroup M}
    (hC : C = fixV K ⊓ commV K) :
    ∃ B, B ≤ autSec Ab (commV K) C ∧ IsFFStarOffender (autSec (K ⊔ T) (commV K) C) B ∧
      B42Conclusion (autSec (K ⊔ T) (commV K) C) (autSec K (commV K) C) B := by
  have hn := normal_L h
  have hLG := le_G h
  have hTG : T ≤ X := hT.1
  have hT2 : IsPGroup 2 T := hT.2.1
  obtain ⟨hUC, hlt, hGU, hGC, hfL, hfM⟩ := secConfig hV h hU hT hC
  have hMG : K ⊔ T ≤ X := sup_le hLG hTG
  have hMU : K ⊔ T ≤ stabSub (commV K) := hMG.trans hGU
  have hMC : K ⊔ T ≤ stabSub C := hMG.trans hGC
  have hAM : IsFFStarOffender (K ⊔ T) Ab := ⟨hAbT.trans le_sup_right, hAb.2.1, hAb.2.2.1, hAb.2.2.2⟩
  obtain ⟨hinv, hcomm, hlt', hirr⟩ := irr_data hU
  have hF : quasithinGenFitting (K ⊔ T) = K := genFitting_sup_eq h hTG hT2
  have hq : CFSG.IsQuasisimple ↥(quasithinGenFitting (K ⊔ T)) := by rw [hF]; exact quasi_L h
  have hS : ¬ commSub (commV K) (quasithinGenFitting (K ⊔ T)) ≤ C := by
    rw [hF, hcomm]
    intro hle
    exact lt_irrefl _ (lt_of_lt_of_le hlt hle)
  obtain ⟨-, ⟨B, hBA, hB⟩, -⟩ := B1_5_8 hV hAM (W := commV K) (U := C) hUC hMU hMC hq
    (pCoreOf_sup_eq_bot h hTG hT2) hS
  refine ⟨B, hBA, hB, ?_⟩
  have hb4 := b4Hyp_section' hV h hU hTG hT2 hC
  exact hB42 (Sec (commV K) C) (sq_eq_one_sec hV _ _) _ _ hb4 B hB

end Abs

end B59

end FFC

end CFSG.Quasithin
