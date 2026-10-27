module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenEightProof
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.ComponentOrbitThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ComponentCalV1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.ACandidateU33

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem gap17_8_psu33 {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) (h17_4 : R17_4AtA D V₀ V hC.hyp125)
    (h127 : R127 D) (h117 : C117 D V₀ V) (hU : UniqueMax D.M L)
    (hK : Inputs1719.K_U33SThreePair) (hK8 : Inputs1719.K_U33AutE8)
    (hTL : D.T ≤ Subgroup.normalizer (L : Set G))
    (hk : D.k = 1) (hU3 : LieModel (Bar2 L) .PSU 3 3 1) : False := by
  have hV := hC.hyp125
  have hnorm : CFSG.Quasithin.imageOTwoQuot D.M D.T ≤
      Subgroup.normalizer (CFSG.Quasithin.imageOTwoQuot D.M L :
        Set (CFSG.Quasithin.OTwoQuot D.M)) :=
    CFSG.Quasithin.S152Y.imageOTwoQuot_le_normalizer (M := D.M) (X := D.T) (Y := L) hTL
  have hnorm' : Tbar9 D ≤ Subgroup.normalizer (K1Nine D L : Set (Mbar9 D)) := hnorm
  obtain ⟨L₁, L₂, hT₁, hT₂, hsup, hq₁, hq₂⟩ :=
    exists_s3_pair_of_calC_bar2 (D := D) (L := L) hC.memL hnorm'
      (fun Y _ _ K S hKY hKe => by
        obtain ⟨e⟩ := hKe
        exact hK Y K S hKY (LieModel.of_mulEquiv e.symm hU3))
  have hcomp : barSub V₀ V hV.isElemAbelian L ∈ compBar D.M V₀ V hV.isElemAbelian :=
    barSub_mem_compBar_of_uniqueMax h127 hV h117 hC.memL hU
  have hU' : UniqueMax D.M (L ⊔ D.T) :=
    uc22p22u_uniqueMax_mono D le_sup_left (sup_le hC.memL.1.le D.sylowM.le) hU
  have hST : D.T ⊓ Subgroup.normalizer (L : Set G) = D.T := inf_eq_left.mpr hTL
  have hk2 : D.k = 2 :=
    h17_4 L L₁ L₂ hC.memL hTL hcomp (by rw [hST]; exact hT₁)
      (by rw [hST]; exact hT₂) (by rw [hST]; exact hsup) hq₁ hq₂
      (Or.inr (aCandLe_two_of_U33 hK8 (lieModel_barInf_of_U33 hC.memL hU3))) hU'
  omega

theorem gap17_8_nonnormal_of {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) (h17_1 : R17_1At D V₀ V hC.hyp125)
    (hU33 : Inputs1719.K_U33Local) (hL33 : Inputs1719.K_L33Local) :
    Gap17_8_nonnormal D V₀ V L r q hC := by
  intro hNT hk htype
  have hK : ∀ (Y : Type) [Group Y] [Finite Y] (K S : Subgroup Y),
      Inputs1719.KYForm Y K S → Nonempty (↥K ≃* Bar2 L) →
      ∃ E : Subgroup Y, E ≤ K ∧ E ≠ ⊥ ∧ IsPGroup 3 ↥E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧
        ¬ E ≤ (Subgroup.center ↥K).map K.subtype ∧ Permutes E S := by
    intro Y _ _ K S hKY hKe
    obtain ⟨e⟩ := hKe
    rcases htype with hL3 | hU3
    · exact hL33 Y K S hKY (LieModel.of_mulEquiv e.symm hL3)
    · exact hU33 Y K S hKY (LieModel.of_mulEquiv e.symm hU3)
  exact hNT (le_normalizer_of_noncentral_three h17_1 hk hC.memL hK)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
