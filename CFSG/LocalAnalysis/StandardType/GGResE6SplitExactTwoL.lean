module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLBstarE6
public import CFSG.LocalAnalysis.StandardType.GGResTwoCells
import CFSG.LocalAnalysis.StandardType.GGResExcSplitExactTwoL
import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMoreE6
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1CenterE6
import CFSG.LocalAnalysis.StandardType.GGResJOpenLabel
import CFSG.LocalAnalysis.StandardType.GGTCJHolds
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGTBE6
import CFSG.LocalAnalysis.StandardType.GGTBTorLiftRowsHolds
import CFSG.LocalAnalysis.StandardType.GGTBTorLiftRowsCls
import CFSG.LocalAnalysis.StandardType.GGIOneFieldCFHolds
import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMoreTypeA
import CFSG.LocalAnalysis.StandardType.GGResHigherFieldI1

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

theorem GGResHyp.bstar_eq_of_e6Split
    {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel GGExcLSplitE6Label p Bs L) :
    B = Bs := by
  have hMark := largeEvenMarking_and_labelAll
    (S := fun lab => GGExcLSplitE6Label p lab)
    (P' := fun R _ I _ =>
      (∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I) ∧
        ∃ r, GGTorusLift p r R ∧ GGINormAbove p r R I)
    (fun lab hlab hS => by
      by_cases hpn : p ∣ lab.n
      · exact largeEvenLabelAll_and
          (largeEvenLabelAll_innerDiagBound_field hp hlab
            (Or.inr (Or.inr (Or.inl ⟨hS.1, hS.2.2, hS.2.1, hpn⟩))))
          (IOneMore.largeEvenLabelAll_normAbove_field hp hlab
            (Or.inr (Or.inr (Or.inl ⟨hS.1, hS.2.2, hS.2.1, hpn⟩))))
      · exact (largeEvenLabelAll_bstarEq_e6Coprime hp hlab ⟨hS.1, hS.2.2, hS.2.1, hpn⟩).mono
          (fun _ _ _ _ ⟨hb, r, hr, hrk⟩ => ⟨hb, r, hr, ggINormAbove_of_iRankLe hp.one_lt hrk⟩))
    (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨hL, lab, -, hraw⟩ := hMark
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, h3Bs⟩, ⟨r₁, hlift₁, hbound⟩, r₂, hlift₂, hnorm⟩ :=
    largeEvenRawDatum_exists hraw
  have hnc := ggLNoncyclicInput_holds G p B x L hH.1.1
  have hBBs : B ≤ Bs := hH.1.2.1.1
  exact bstar_eq_of_bound_norm hH.1.1 hH.1.2.1 hnc hL θ
    (hBBs.trans hBsN) (fun b hb => h3Bs b (hBBs hb)) hlift₁ hbound hlift₂ hnorm

theorem GGResHyp.false_of_exact2_L_e6Split
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel GGExcLSplitE6Label p Bs L)
    (hD : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) : False := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hT : GGTBTorAll := ggTBTorAll_of_remaining trivial
  have hB : B = Bs := hH.bstar_eq_of_e6Split hp hM
  have hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) = D := hH.iOne_of_eq_bstar hB
  have hrow : ∀ lab : LargeEvenLabel, GGExcLSplitE6Label p lab →
      ∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ) (M : CoxeterMatrix (Fin N)),
        GGTBTorRowAt p lab r m N C M ∧ 6 ≤ r := by
    rintro lab ⟨ht, hp3, hpq⟩
    have hEnn : ggTorEnn p lab = 0 := ggTorEnn_eq_zero_of_dvd_sub_one hp hp2 hpq
    have hm : p ∣ ggTorM lab := by
      simpa [ggTorM, ht] using hpq
    exact ⟨_, _, _, _, _, GGTBTorRowAt.e6Ind hp3 (Or.inl ht) hm, by omega⟩
  have hm7 : 7 ≤ LargeEvenTwoLocalRank p G := by
    obtain ⟨_, r, _, _, _, _, _, _, θ, _, _, hperf, -, -, hr6, -, hlift, -, -⟩ :=
      l05nPlQ_marking_with (ggTBTorWRows_of_all hT) ggTBTorLiftRows_holds hp2
        (fun r _ _ _ _ => 6 ≤ r) (GGInnerDiagOnLabel.mono_label (fun lab h => hrow lab h) hM)
    have := hH.succ_le_twoLocalRank_of_torusLift_L hperf θ hlift
    omega
  have hMc : GGInnerDiagOnLabel (fun p lab => S2MathAs51642Interfaces.CenterPrimeTo p lab ∧
      (lab.tag = .E6 ∨ lab.tag = .twE6)) p Bs L :=
    GGInnerDiagOnLabel.mono_label (fun lab h => by
        obtain ⟨ht, hp3, -⟩ := h
        refine ⟨⟨?_, ?_⟩, Or.inl ht⟩
        · simp [S2MathAs51642Interfaces.SmallDerived, ht]
        · simp [ht, hp3]) hM
  have hJ : GGInnerDiagOn Bs J := q1CenterPrimeE6TwE6_holds G p B Bs x L D J hH.1 hMc
  have hJlab : GGInnerDiagOnLabel (fun _ _ => True) p Bs J :=
    (GGInnerDiagOn.label (fun _ _ => True) p hJ).mono_label (fun _ _ => trivial)
  have hfwd := hH.fix_mem_centralizer_J_of_tcj_of_seven hT ggTBTorLiftRows_holds
    TCJ.ggTCJKnown_holds ggLabelRigidInput_holds hm7 hJlab
  have hL : GGInnerDiagOnLabel (fun p lab => GGTBTorCov p lab ∧ ¬ ggSingularBaseLabel p lab)
      p Bs L :=
    GGInnerDiagOnLabel.mono_label (fun lab h => by
        obtain ⟨r, m, N, C, M, hr, -⟩ := hrow lab h
        refine ⟨⟨r, m, N, C, M, hr⟩, ?_⟩
        obtain ⟨ht, hp3, -⟩ := h
        simp [ggSingularBaseLabel, ht, hp3]) hM
  exact hH.false_of_exact2_nonsingular_L hT ggTBTorLiftRows_holds hfwd hL hI1 hD

theorem ggResMultiNodeRestTwoCellInput_e6Split :
    GGResMultiNodeRestTwoCellInput GGExcLSplitE6Label := by
  apply GGResMultiNodeRestTwoCellInput.of_false
  intro G _ _ p _ B Bs x L D J y K hH hL hD
  exact hH.false_of_exact2_L_e6Split hL hD

end CFSG.StandardType

end
