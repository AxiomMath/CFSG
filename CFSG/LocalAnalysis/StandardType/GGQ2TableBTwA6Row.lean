module

public import CFSG.LocalAnalysis.StandardType.GGQ2TableBTwA3Row
public import Certificates.Certificate1952
import CFSG.LocalAnalysis.StandardType.GGTBTorAIndUFourTwo
import CFSG.LocalAnalysis.StandardType.GGTDLabels
import CFSG.LocalAnalysis.StandardType.GGTBTorCHolds
import CFSG.LocalAnalysis.StandardType.GGTBTorD
import CFSG.LocalAnalysis.StandardType.GGTBTorRelDHolds
import CFSG.LocalAnalysis.StandardType.GGTBTorE7
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosWeylSys
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
import CFSG.LocalAnalysis.StandardType.GGCoxeterForkProofBCDExt
import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallE8
import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallRankDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGQ2TwA6TwoLabel (lab : LargeEvenLabel) : Prop :=
  lab = ⟨.twA, 7, 1⟩ ∨ lab = ⟨.twA, 8, 1⟩ ∨ lab = ⟨.C, 7, 1⟩ ∨ lab = ⟨.twD, 7, 1⟩ ∨
    lab = ⟨.twD, 8, 1⟩ ∨ lab = ⟨.E7, 0, 1⟩

theorem GGQ2TwA6TwoLabel.inLambda2 {lab : LargeEvenLabel} (h : GGQ2TwA6TwoLabel lab) :
    LargeEvenInLambda2 lab := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [LargeEvenInLambda2]

theorem largeEvenLabelAll_twA7_two_torW :
    LargeEvenLabelAll ⟨.twA, 7, 1⟩ fun R _ I _ =>
      GGTorusTorW 3 6 3 7 (CartanMatrix.A 7) (CoxeterMatrix.A 7) R I := by
  have hE : ggTorEnn 3 ⟨.twA, 7, 1⟩ = 1 := by norm_num [ggTorEnn]
  have hM : ggTorM ⟨.twA, 7, 1⟩ = 3 := by norm_num [ggTorM]
  have hΛ : LargeEvenInLambda2 ⟨.twA, 7, 1⟩ := by
    unfold LargeEvenInLambda2
    norm_num
  have h := ggTBTorAInd_holds 3 (by norm_num) (by norm_num) ⟨.twA, 7, 1⟩ hΛ
    (Or.inr rfl) (by norm_num) (by rw [hM])
  simpa [hE, hM] using h

theorem largeEvenLabelAll_twA8_two_torW :
    LargeEvenLabelAll ⟨.twA, 8, 1⟩ fun R _ I _ =>
      GGTorusTorW 3 6 3 8 (CartanMatrix.A 8) (CoxeterMatrix.A 8) R I := by
  have hE : ggTorEnn 3 ⟨.twA, 8, 1⟩ = 1 := by norm_num [ggTorEnn]
  have hM : ggTorM ⟨.twA, 8, 1⟩ = 3 := by norm_num [ggTorM]
  have hΛ : LargeEvenInLambda2 ⟨.twA, 8, 1⟩ := by
    unfold LargeEvenInLambda2
    norm_num
  have h := ggTBTorA_holds 3 (by norm_num) (by norm_num) ⟨.twA, 8, 1⟩ hΛ
    (Or.inr rfl) (by norm_num) (by norm_num) (by rw [hM])
    (by rintro ⟨-, h5, -⟩; simp at h5)
  simpa [hE, hM] using h

theorem largeEvenLabelAll_C7_two_torW :
    LargeEvenLabelAll ⟨.C, 7, 1⟩ fun R _ I _ =>
      GGTorusTorW 3 6 3 7 (CartanMatrix.C 7) (CoxeterMatrix.B 7) R I := by
  have hE : ggTorEnn 3 ⟨.C, 7, 1⟩ = 1 := by norm_num [ggTorEnn]
  have hM : ggTorMpm 3 ⟨.C, 7, 1⟩ = 3 := by norm_num [ggTorMpm]
  have hΛ : LargeEvenInLambda2 ⟨.C, 7, 1⟩ := by
    unfold LargeEvenInLambda2
    norm_num
  have h := ggTBTorC_holds 3 (by norm_num) (by norm_num) ⟨.C, 7, 1⟩ hΛ
    (Or.inr rfl) (by norm_num)
  simpa [hE, hM] using h

theorem largeEvenLabelAll_twD7_two_torW :
    LargeEvenLabelAll ⟨.twD, 7, 1⟩ fun R _ I _ =>
      GGTorusTorW 3 6 3 7 (CartanMatrix.D 7) (ggCoxeterMatrixD 7) R I := by
  have hE : ggTorEnn 3 ⟨.twD, 7, 1⟩ = 1 := by norm_num [ggTorEnn]
  have hM : ggTorMpm 3 ⟨.twD, 7, 1⟩ = 3 := by norm_num [ggTorMpm]
  have hΛ : LargeEvenInLambda2 ⟨.twD, 7, 1⟩ := by
    unfold LargeEvenInLambda2
    norm_num
  have h := ggTBTorD_holds 3 (by norm_num) (by norm_num) ⟨.twD, 7, 1⟩ hΛ
    (Or.inr ⟨rfl, by norm_num, by norm_num⟩)
  simpa [hE, hM] using h

theorem largeEvenLabelAll_twD8_two_torW :
    LargeEvenLabelAll ⟨.twD, 8, 1⟩ fun R _ I _ =>
      GGTorusTorW 3 7 3 7 (CartanMatrix.B 7) (CoxeterMatrix.B 7) R I := by
  have hM : ggTorMpm 3 ⟨.twD, 8, 1⟩ = 3 := by norm_num [ggTorMpm]
  have hΛ : LargeEvenInLambda2 ⟨.twD, 8, 1⟩ := by
    unfold LargeEvenInLambda2
    norm_num
  have h := ggTBTorRelD_holds 3 (by norm_num) (by norm_num) ⟨.twD, 8, 1⟩ hΛ
    (Or.inr ⟨rfl, Or.inr ⟨by norm_num, by norm_num⟩⟩)
  simpa [hM] using h

theorem largeEvenLabelAll_E7_two_torW :
    LargeEvenLabelAll ⟨.E7, 0, 1⟩ fun R _ I _ =>
      GGTorusTorW 3 6 3 7 (CartanMatrix.E 7) CoxeterMatrix.E₇ R I := by
  have hE : ggTorEnn 3 ⟨.E7, 0, 1⟩ = 1 := by norm_num [ggTorEnn]
  have hM : ggTorMpm 3 ⟨.E7, 0, 1⟩ = 3 := by norm_num [ggTorMpm]
  have hΛ : LargeEvenInLambda2 ⟨.E7, 0, 1⟩ := by
    unfold LargeEvenInLambda2
    norm_num
  have h := ggTBTorE7_holds 3 (by norm_num) (by norm_num) ⟨.E7, 0, 1⟩ hΛ rfl (by norm_num)
  simpa [hE, hM] using h

theorem exists_ggQ2LDatum_of_twA6Label
    [Fact (Nat.Prime 3)] (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig 3 B Bs x L D J)
    {X : Subgroup G} {u : G} (hu1 : u ≠ 1)
    (hBX : Bs ⊓ Subgroup.centralizer (X : Set G) = Subgroup.zpowers u)
    (hInn : GGInnerDiagOn Bs X) {labX : LargeEvenLabel} (hlab : GGQ2TwA6TwoLabel labX)
    (hhasX : GGHasLabel labX (↥X ⧸ Subgroup.center ↥X))
    (hr : ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G), 3 ^ 7 ≤ Nat.card (ggGamma X hN).range) :
    ∃ M : GGQ2LDatum 3 Bs X u, M.Shape := by
  have hmk := ggInnerDiagOn_relabel hRig hInn hlab.inLambda2 hhasX
  have hMark : GGInnerDiagOnLabel (fun _ lab => lab = labX) 3 Bs X :=
    largeEvenMarking_mono (fun lab R _ I F θ hP => ⟨hP.1, hP.2⟩) hmk
  have hr6 : ∀ hN : Bs ≤ Subgroup.normalizer (X : Set G),
      3 ^ 6 ≤ Nat.card (ggGamma X hN).range :=
    fun hN => (Nat.pow_le_pow_right (by norm_num) (by norm_num : 6 ≤ 7)).trans (hr hN)
  rcases hlab with rfl | rfl | rfl | rfl | rfl | rfl
  · exact exists_ggQ2LDatum_of_markTorW (s := 6) hcfg hu1 hBX hMark (by norm_num)
      (CFSG.TwoNodeSmall.pws_ggIsWeylMatrix_A 7 (by norm_num)) (ggIntCartan_A 7)
      (fun lab _ h => h ▸ largeEvenLabelAll_twA7_two_torW) hr6
      (lab' := ⟨.twA, 7, 1⟩) ⟨Equiv.refl _, rfl⟩
  · exact exists_ggQ2LDatum_of_markTorW (s := 6) hcfg hu1 hBX hMark (by norm_num)
      (CFSG.TwoNodeSmall.pws_ggIsWeylMatrix_A 8 (by norm_num)) (ggIntCartan_A 8)
      (fun lab _ h => h ▸ largeEvenLabelAll_twA8_two_torW) hr6
      (lab' := ⟨.twA, 8, 1⟩) ⟨Equiv.refl _, rfl⟩
  · exact exists_ggQ2LDatum_of_markTorW (s := 6) hcfg hu1 hBX hMark (by norm_num)
      (CFSG.TwoNodeSmall.pws_ggIsWeylMatrix_B 7 (by norm_num)) (ggIntCartan_C 7)
      (fun lab _ h => h ▸ largeEvenLabelAll_C7_two_torW) hr6
      (lab' := ⟨.C, 7, 1⟩) ⟨Equiv.refl _, rfl⟩
  · exact exists_ggQ2LDatum_of_markTorW (s := 6) hcfg hu1 hBX hMark (by norm_num)
      (CFSG.TwoNodeSmall.pws_ggIsWeylMatrix_D 7 (by norm_num)) (ggIntCartan_D 7)
      (fun lab _ h => h ▸ largeEvenLabelAll_twD7_two_torW) hr6
      (lab' := ⟨.twD, 7, 1⟩) ⟨Equiv.refl _, rfl⟩
  · exact exists_ggQ2LDatum_of_markTorW (s := 7) hcfg hu1 hBX hMark (by norm_num)
      (CFSG.TwoNodeSmall.pws_ggIsWeylMatrix_B 7 (by norm_num)) (ggIntCartan_B 7)
      (fun lab _ h => h ▸ largeEvenLabelAll_twD8_two_torW) hr
      (lab' := ⟨.B, 7, 1⟩) ⟨Equiv.refl _, rfl⟩
  · exact exists_ggQ2LDatum_of_markTorW (s := 6) hcfg hu1 hBX hMark (by norm_num)
      (CFSG.TwoNodeSmall.pws_ggIsWeylMatrix_E7) (ggIntCartan_E₇)
      (fun lab _ h => h ▸ largeEvenLabelAll_E7_two_torW) hr6
      (lab' := ⟨.E7, 0, 1⟩) ⟨Equiv.refl _, rfl⟩

end CFSG.StandardType

end
