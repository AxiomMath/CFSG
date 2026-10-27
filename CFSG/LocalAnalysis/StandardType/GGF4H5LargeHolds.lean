module

public import Certificates.Certificate13604
public import CFSG.LocalAnalysis.StandardType.GGF4LabelH5Pieces
public import CFSG.LocalAnalysis.StandardType.GGRealKG
public import CFSG.LocalAnalysis.StandardType.GGRealKGFiveClassical
public import CFSG.LocalAnalysis.StandardType.GGRealKGThreeClassical
import CFSG.LocalAnalysis.StandardType.GGRealKGThreeAssembly
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGExclNoIso

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem n_ge_two_of_ggLabelIso_C {f : ℕ} (hf : 2 ≤ f) :
    ∀ lab : LargeEvenLabel, GGLabelIso ⟨.C, 3, f⟩ lab → 2 ≤ lab.n := by
  rintro lab (h | ⟨-, -, -, hn⟩ | h | h | h | h | h | h)
  · rw [← h]; exact hf
  · dsimp only at hn; omega
  all_goals simp [LargeEvenLabel.mk.injEq] at h

private theorem n_ge_two_of_ggLabelIso_twD {f : ℕ} (hf : 2 ≤ f) :
    ∀ lab : LargeEvenLabel, GGLabelIso ⟨.twD, 4, f⟩ lab → 2 ≤ lab.n := by
  rintro lab (h | h | h | h | h | h | h | h)
  · rw [← h]; exact hf
  all_goals simp [LargeEvenLabel.mk.injEq] at h

private theorem n_ge_two_of_ggLabelIso_twA {f : ℕ} (hf : 2 ≤ f) :
    ∀ lab : LargeEvenLabel, GGLabelIso ⟨.twA, 5, f⟩ lab → 2 ≤ lab.n := by
  rintro lab (h | h | h | h | h | h | h | h)
  · rw [← h]; exact hf
  all_goals simp [LargeEvenLabel.mk.injEq] at h

private theorem largeEvenInLambda2_C_three {f : ℕ} (hf : 2 ≤ f) :
    LargeEvenInLambda2 ⟨.C, 3, f⟩ := by
  dsimp only [LargeEvenInLambda2]
  exact ⟨by omega, by omega, by omega⟩

private theorem largeEvenInLambda2_twD_four {f : ℕ} (hf : 2 ≤ f) :
    LargeEvenInLambda2 ⟨.twD, 4, f⟩ := by
  dsimp only [LargeEvenInLambda2]
  exact ⟨by omega, by omega⟩

private theorem largeEvenInLambda2_twA_five {f : ℕ} (hf : 2 ≤ f) :
    LargeEvenInLambda2 ⟨.twA, 5, f⟩ := by
  dsimp only [LargeEvenInLambda2]
  exact ⟨by omega, by omega, by omega⟩

private theorem innerDiagOnLabel_qFourClass_of_row (hRig : GGLabelRigidInput) {G : Type} [Group G]
    {p : ℕ} {Bs K : Subgroup G} (hK : GGInnerDiagOn Bs K) {lab₀ : LargeEvenLabel}
    (hl₀ : LargeEvenInLambda2 lab₀) (h₀ : GGHasLabel lab₀ (↥K ⧸ Subgroup.center ↥K))
    (hn : ∀ lab : LargeEvenLabel, GGLabelIso lab₀ lab → 2 ≤ lab.n)
    (hT₀ : GGRealClassTag lab₀.tag) :
    GGInnerDiagOnLabel (fun p lab => GGLabQFour p lab ∧ GGRealClassTag lab.tag) p Bs K := by
  obtain ⟨hX, lab, hlab, hraw⟩ := hK
  have has : GGHasLabel lab (↥K ⧸ Subgroup.center ↥K) := by
    unfold GGHasLabel
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨-, -, θ, -⟩
    exact ⟨θ⟩
  have hiso := hRig lab₀ lab _ hl₀ hlab h₀ has
  exact ⟨hX, lab, hlab,
    largeEvenRawDatum_mono (fun R _ I F ⟨hs, hna, θ, hP⟩ =>
      ⟨hs, hna, θ, ⟨hn lab hiso, ggRealClassTag_of_labelIso hiso hT₀⟩, hP⟩) hraw⟩

theorem ggF4H5Large_of_real
    (hRig : GGLabelRigidInput) (h3 : GGReflRealizedQFourInputThreeClassical)
    (h5 : GGReflRealizedQFourInputFiveClassical) : GGF4H5Large := by
  intro G _ _ p B Bs x L D J ks hres hB K hK hrow
  have hcfg : GGConfig p B Bs x L D J := hres.1.1.1
  have hInn : GGInnerDiagAll p B Bs x L D J := hres.1.1.2.2.1
  have hNT : GGNoTransvection p Bs := hres.1.1.2.2.2.1
  obtain ⟨y, hnb⟩ := hres.1.2.2.2.1.2 K hK
  have hmark : GGInnerDiagOn Bs K := hInn.2 y K hnb
  have hdata : ∃ lab₀ : LargeEvenLabel, LargeEvenInLambda2 lab₀ ∧
      GGHasLabel lab₀ (↥K ⧸ Subgroup.center ↥K) ∧
      (∀ lab : LargeEvenLabel, GGLabelIso lab₀ lab → 2 ≤ lab.n) ∧ GGRealClassTag lab₀.tag := by
    rcases hrow with ⟨f, hf, -, -, hKlab⟩ | ⟨f, hf, -, -, hKlab⟩ |
      ⟨f, hf, -, -, hKlab⟩ | ⟨f, hf, -, -, hKlab⟩ | ⟨f, hf, -, -, hKlab⟩
    · exact ⟨⟨.C, 3, f⟩, largeEvenInLambda2_C_three hf, hKlab,
      n_ge_two_of_ggLabelIso_C hf, by simp [GGRealClassTag]⟩
    · exact ⟨⟨.twD, 4, f⟩, largeEvenInLambda2_twD_four hf, hKlab,
      n_ge_two_of_ggLabelIso_twD hf, by simp [GGRealClassTag]⟩
    · exact ⟨⟨.C, 3, f⟩, largeEvenInLambda2_C_three hf, hKlab,
      n_ge_two_of_ggLabelIso_C hf, by simp [GGRealClassTag]⟩
    · exact ⟨⟨.twD, 4, f⟩, largeEvenInLambda2_twD_four hf, hKlab,
      n_ge_two_of_ggLabelIso_twD hf, by simp [GGRealClassTag]⟩
    · exact ⟨⟨.twA, 5, f⟩, largeEvenInLambda2_twA_five hf, hKlab,
      n_ge_two_of_ggLabelIso_twA hf, by simp [GGRealClassTag]⟩
  obtain ⟨lab₀, hl₀, h₀, hn, hT₀⟩ := hdata
  have hlabKc :
      GGInnerDiagOnLabel (fun p lab => GGLabQFour p lab ∧ GGRealClassTag lab.tag) p Bs K :=
    innerDiagOnLabel_qFourClass_of_row hRig hmark hl₀ h₀ hn hT₀
  have hp : p.Prime := hcfg.tableB_facts.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hp_or : p = 3 ∨ 5 ≤ p := by
    have h3le : 3 ≤ p := by
      have h := hp.two_le
      omega
    rcases lt_or_eq_of_le h3le with h | h
    · right
      obtain ⟨k, hk⟩ := hp.eq_two_or_odd'.resolve_left hp2
      omega
    · left
      exact h.symm
  rcases hp_or with hp3 | hp5
  · exact h3 G p B Bs x L D J hcfg hInn hNT hp3 K (Or.inr ⟨y, hnb⟩) hlabKc
  · exact h5 G p B Bs x L D J hcfg hInn hNT hp5 K (Or.inr ⟨y, hnb⟩) hlabKc

section H5LargeHolds

theorem ggF4H5Large_holds
    (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput) : GGF4H5Large := by
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hraw : GGRawInnFieldInput := ggRawInnFieldInput_holds
  have hiso : GGRawInndiagIsoInput :=
    ggRawInndiagIsoInput_of_rest
      (ggRawInndiagIsoRestInput_of_round5 ggRawInndiagIsoRound5_holds)
  exact
    ggF4H5Large_of_real hRig
      ((ggReflRealizedQFourInputThree_of_jgeom hLB hSP).classical)
      (ggReflRealizedQFourInputFiveClassical_holds hRig hraw hiso)

theorem ggF4LabelH5_of_pos
    (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) : GGF4LabelH5 :=
  ggF4LabelH5_of_pieces ggF4H5Core_holds hL hP (ggF4H5Large_holds hL hP)

end H5LargeHolds

end CFSG.StandardType

end
