module

public import CFSG.LocalAnalysis.StandardType.GGResNonsingularBase
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLBstar
import CFSG.LocalAnalysis.StandardType.GGResJOpenLabel
import CFSG.LocalAnalysis.StandardType.GGTCJHolds
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGTBE6
import CFSG.LocalAnalysis.StandardType.GGTBTorLiftRowsHolds
import CFSG.LocalAnalysis.StandardType.GGTBTorLiftRowsCls
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1E7
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1E8
import CFSG.LocalAnalysis.StandardType.GGIOneFieldCFHolds
import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperRestExc
import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMoreTypeA
import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagTwE6
import CFSG.LocalAnalysis.StandardType.GGResHigherFieldI1
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeABridge

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

theorem GGResHyp.bstar_eq_of_excLSplit
    {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hRig : GGInnerDiagOnLabel GGExcLSplitLabel p Bs L) :
    B = Bs := by
  have hMark := largeEvenMarking_and_labelAll
    (S := fun lab => GGExcLSplitLabel p lab)
    (P' := fun R _ I _ =>
      (∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I) ∧
        ∃ r, GGTorusLift p r R ∧ GGINormAbove p r R I)
    (fun lab hlab hS => by
      by_cases hpn : p ∣ lab.n
      · exact largeEvenLabelAll_and
          (largeEvenLabelAll_innerDiagBound_field hp hlab
            (Or.inr (Or.inr (Or.inr ⟨hS.1, hS.2, hpn⟩))))
          (IOneMore.largeEvenLabelAll_normAbove_field hp hlab
            (Or.inr (Or.inr (Or.inr ⟨hS.1, hS.2, hpn⟩))))
      · exact (largeEvenLabelAll_bstarEq_excSplit hp hlab ⟨hS.1, hS.2, hpn⟩).mono
          (fun _ _ _ _ ⟨hb, r, hr, hrk⟩ => ⟨hb, r, hr, ggINormAbove_of_iRankLe hp.one_lt hrk⟩))
    (fun _ _ _ _ _ _ hP => hP.1) hRig
  obtain ⟨hL, lab, -, hraw⟩ := hMark
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, h3Bs⟩, ⟨r₁, hlift₁, hbound⟩, r₂, hlift₂, hnorm⟩ :=
    largeEvenRawDatum_exists hraw
  have hnc := ggLNoncyclicInput_holds G p B x L hH.1.1
  have hBBs : B ≤ Bs := hH.1.2.1.1
  exact bstar_eq_of_bound_norm hH.1.1 hH.1.2.1 hnc hL θ
    (hBBs.trans hBsN) (fun b hb => h3Bs b (hBBs hb)) hlift₁ hbound hlift₂ hnorm

theorem GGResHyp.false_of_exact2_nonsingular_L
    (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hfwd : ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G))
    (hL : GGInnerDiagOnLabel (fun p lab => GGTBTorCov p lab ∧ ¬ ggSingularBaseLabel p lab)
      p Bs L)
    (hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) = D)
    (hD : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) : False := by
  have hfixJ : ∀ b : ↥Bs,
      (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔ (b : G) ∈ Subgroup.centralizer (J : Set G) := by
    intro b
    refine ⟨hfwd b, fun hb φ hφ => ?_⟩
    apply ggAutomizer_apply_eq_of_le_centralizer (H := J) (x := b) _ hφ
    intro j hj
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [Subgroup.mem_centralizer_iff] at hb
    exact hb j hj
  exact hH.false_of_singular_card_nonsingular_L hT hLift hL
    (GGResLeviDatumCard.singular_card (ggResExact2_typed_dichotomy_L_of_fixed hH hI1 hfixJ hD))

theorem GGResHyp.false_of_exact2_L_excSplit78
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun p lab => (lab.tag = .E7 ∨ lab.tag = .E8) ∧ p ∣ 2 ^ lab.n - 1) p Bs L)
    (hD : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) : False := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hT : GGTBTorAll := ggTBTorAll_of_remaining trivial
  have hB : B = Bs := hH.bstar_eq_of_excLSplit hp (GGInnerDiagOnLabel.mono_label
    (fun lab h => ⟨h.1.elim Or.inl (fun h8 => Or.inr (Or.inl h8)), h.2⟩) hM)
  have hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) = D := hH.iOne_of_eq_bstar hB
  have hrow : ∀ lab : LargeEvenLabel, (lab.tag = .E7 ∨ lab.tag = .E8) → p ∣ 2 ^ lab.n - 1 →
      ∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ) (M : CoxeterMatrix (Fin N)),
        GGTBTorRowAt p lab r m N C M ∧ 7 ≤ r := by
    intro lab ht hpq
    have hEnn : ggTorEnn p lab = 0 := ggTorEnn_eq_zero_of_dvd_sub_one hp hp2 hpq
    have hdvd : p ∣ (2 ^ lab.n - 1) * (2 ^ lab.n + 1) := dvd_mul_of_dvd_left hpq _
    rcases ht with h7 | h8
    · exact ⟨_, _, _, _, _, GGTBTorRowAt.e7 h7 hdvd, by omega⟩
    · by_cases hp3 : p = 3
      · subst hp3
        exact ⟨_, _, _, _, _, GGTBTorRowAt.e8Three h8 rfl, by omega⟩
      · exact ⟨_, _, _, _, _, GGTBTorRowAt.e8Ind hp3 h8 hdvd, by omega⟩
  have hm7 : 7 ≤ LargeEvenTwoLocalRank p G := by
    obtain ⟨_, r, _, _, _, _, _, _, θ, _, _, hperf, -, -, hr7, -, hlift, -, -⟩ :=
      l05nPlQ_marking_with (ggTBTorWRows_of_all hT) ggTBTorLiftRows_holds hp2
        (fun r _ _ _ _ => 7 ≤ r)
        (GGInnerDiagOnLabel.mono_label (fun lab h => hrow lab h.1 h.2) hM)
    have := hH.succ_le_twoLocalRank_of_torusLift_L hperf θ hlift
    omega
  have hJ : GGInnerDiagOn Bs J := by
    rcases GGInnerDiagOnLabel.elim_or (S := fun _ lab => lab.tag = .E7)
        (T := fun _ lab => lab.tag = .E8)
        (GGInnerDiagOnLabel.mono_label (fun _ h => h.1) hM) with h7 | h8
    · exact q1E7InnerDiag_holds G p B Bs x L D J hH.1 h7
    · exact q1E8InnerDiag_holds G p B Bs x L D J hH.1 h8
  have hJlab : GGInnerDiagOnLabel (fun _ _ => True) p Bs J :=
    (GGInnerDiagOn.label (fun _ _ => True) p hJ).mono_label (fun _ _ => trivial)
  have hfwd := hH.fix_mem_centralizer_J_of_tcj_of_seven hT ggTBTorLiftRows_holds
    TCJ.ggTCJKnown_holds ggLabelRigidInput_holds hm7 hJlab
  have hL : GGInnerDiagOnLabel (fun p lab => GGTBTorCov p lab ∧ ¬ ggSingularBaseLabel p lab)
      p Bs L := GGInnerDiagOnLabel.mono_label (fun lab h => by
        obtain ⟨r, m, N, C, M, hr, -⟩ := hrow lab h.1 h.2
        refine ⟨⟨r, m, N, C, M, hr⟩, ?_⟩
        rcases h.1 with ht | ht <;> simp [ggSingularBaseLabel, ht]) hM
  exact hH.false_of_exact2_nonsingular_L hT ggTBTorLiftRows_holds hfwd hL hI1 hD

end CFSG.StandardType

end
