module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseXL48NbrFieldD4
public import CFSG.LocalAnalysis.StandardType.GGInndiagCommRest
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw
public import CFSG.LocalAnalysis.StandardType.GGExclNoIso

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggRawFieldNotComm_of_inndiagComm {p : ℕ} {R : Type} [Group R] {I F : Set (MulAut R)}
    (hEq : GGInndiagCommEq R I F) (hmul : ∀ φ ∈ I, ∀ ψ ∈ I, φ * ψ ∈ I)
    (hinv : ∀ φ ∈ I, φ⁻¹ ∈ I) (hinn : ∀ r : R, MulAut.conj r ∈ I)
    (hF : ∀ f ∈ F, orderOf f = p → f ∉ I) : GGRawFieldNotComm p R I F := by
  intro f hf hord hfT
  have hEq' : ggInndiag R I = ggInndiagComm R := hEq
  have hle : ⁅(⊤ : Subgroup (MulAut R)), ⊤⁆ ≤ ggInndiag R I := by
    rw [hEq']
    exact le_sup_right
  rw [sup_eq_left.mpr hle, ggL45_mem_ggInndiag_iff hmul hinv hinn] at hfT
  exact hF f hf hord hfT

theorem largeEvenLabelAll_fieldNotComm_of_comm {p : ℕ} {lab : LargeEvenLabel}
    (hC : LargeEvenLabelAll lab (LargeEvenSimpleGuard GGInndiagCommEq))
    (hR : LargeEvenLabelAll lab (GGRawInnField p)) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard (GGRawFieldNotComm p)) := by
  intro Q hQ
  refine largeEvenRawDatum_mono ?_ (largeEvenLabelAll_and hC hR Q hQ)
  rintro R _ I F ⟨hQ, hEq, hRIF⟩
  refine ⟨hQ, fun hs hna => ?_⟩
  obtain ⟨hmul, hinv, hinn, hF⟩ := hRIF hs hna
  exact ggRawFieldNotComm_of_inndiagComm (hEq hs hna) hmul hinv hinn hF

theorem largeEvenLabelAll_fieldNotComm_b2der {p : ℕ} (hp : p ≠ 1) {lab : LargeEvenLabel}
    (h : GGB2derLabel lab) : LargeEvenLabelAll lab (LargeEvenSimpleGuard (GGRawFieldNotComm p)) :=
  largeEvenLabelAll_b2der h fun _ _ _ hK _ _ f hf hord _ => hp (by
    rw [← hord, matFieldImage_eq_one_of_card_two hK _ hf, orderOf_one])

section Holds

theorem ggRawFieldNotCommInput_holds : GGRawFieldNotCommInput := by
  intro p hp hp2 lab hlab
  have hp1 : p ≠ 1 := hp.one_lt.ne'
  by_cases hD4 : lab.tag = .D ∧ lab.rank = 4
  · exact largeEvenLabelAll_fieldNotComm_dFour hp1 hD4.1 hD4.2
  by_cases hB : lab.tag = .B2der
  · exact largeEvenLabelAll_fieldNotComm_b2der hp1 hB
  have hX : ¬ GGInndiagCommExclLabel lab := by
    rintro (h | h)
    · exact hD4 h
    · exact hB h
  refine largeEvenLabelAll_fieldNotComm_of_comm ?_ (ggRawInnFieldInput_holds p hp hp2 lab hlab)
  by_cases hP : GGInndiagCommProvedLabel lab
  · exact largeEvenLabelAll_inndiagComm_proved hlab hP
  · exact ggInndiagCommRestInput_holds lab hlab hX hP

theorem ggL48NbrFieldInput_holds : GGL48NbrFieldInput :=
  ggL48NbrFieldInput_of_raw ggRawInnFieldInput_holds
    (ggRawInndiagIsoInput_of_rest (ggRawInndiagIsoRestInput_of_round5 ggRawInndiagIsoRound5_holds))
    ggRawFieldNotCommInput_holds

end Holds

end CFSG.StandardType
