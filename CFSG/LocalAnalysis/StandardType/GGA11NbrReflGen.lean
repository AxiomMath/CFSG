module

public import CFSG.LocalAnalysis.StandardType.GGA11NbrDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylKnownDefs
public import CFSG.LocalAnalysis.StandardType.GGA8NbrCoordLift

public section

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.A8Coord Matrix

namespace CFSG.StandardType.A11

private theorem a11nr_ggLabelIso_twD43 {lab : LargeEvenLabel}
    (h : GGLabelIso lab ⟨.twD, 4, 3⟩) : lab = ⟨.twD, 4, 3⟩ := by
  obtain ⟨t, r, n⟩ := lab
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

theorem a11NbrReflGenInput_holds
    : A11NbrReflGenInput := by
  intro hTB hNS hRig hMp hLB G _ _ B Bs x L D J y K φ₃ f n Φ ρ hctx y' K' hnb hlab
  have hcfg : GGConfig 7 B Bs x L D J := hctx.1.1
  have hNoTr : GGNoTransvection 7 Bs := hctx.1.2.2.2.1
  have hInn : GGInnerDiagOn Bs K' := hctx.1.2.2.1.2 y' K' hnb
  have hInnL : GGInnerDiagOn Bs L := hctx.1.2.2.1.1
  have hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 3 := hctx.2.1.2.1
  have h7J : 7 ∣ Nat.card J := hctx.2.2.2.1.1
  have hCJ : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D :=
    ggA8Nbr_bstar_inf_centralizer_J_le hMp hcfg hInnL hmod hnb
  have hJK : J ≤ K' := le_of_ggNbr hLB hcfg.1 hcfg.2.2 h7J hnb
  have hZ : Nat.card ↥(Bs ⊓ K' ⊓ Subgroup.centralizer (K' : Set G)) ≤ 7 := by
    have hle : (Bs ⊓ K' ⊓ Subgroup.centralizer (K' : Set G)) ≤
        Bs ⊓ Subgroup.centralizer (K' : Set G) := inf_le_inf inf_le_left le_rfl
    calc Nat.card ↥(Bs ⊓ K' ⊓ Subgroup.centralizer (K' : Set G))
        ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (K' : Set G)) := Subgroup.card_le_of_le hle
      _ = 7 := GGNbr.card_bstar_inf_centralizer hcfg hnb hCJ hJK
  rcases hlab with hA | hC | htwD
  · have hsp : LargeEvenMarking ↥K' (fun lab _ _ _ _ _ => GGNbrSplitLabel 7 lab) := by
      have hmark := ggInnerDiagOn_relabel hRig hInn (lab := ⟨.A, 3, 3⟩)
        (by norm_num [LargeEvenInLambda2]) hA
      exact largeEvenMarking_mono (fun lab R _ I F θ hP => by
        rw [hP.1]; norm_num [GGNbrSplitLabel, LargeEvenUntwisted]) hmark
    exact ggNbrReflGen_of_halfSplit hTB hRig hcfg hNoTr hnb hInn hsp hZ
  · have hsp : LargeEvenMarking ↥K' (fun lab _ _ _ _ _ => GGNbrSplitLabel 7 lab) := by
      have hmark := ggInnerDiagOn_relabel hRig hInn (lab := ⟨.C, 3, 3⟩)
        (by norm_num [LargeEvenInLambda2]) hC
      exact largeEvenMarking_mono (fun lab R _ I F θ hP => by
        rw [hP.1]; norm_num [GGNbrSplitLabel, LargeEvenUntwisted]) hmark
    exact ggNbrReflGen_of_halfSplit hTB hRig hcfg hNoTr hnb hInn hsp hZ
  · have hmark2 : LargeEvenMarking ↥K' (fun lab _ _ _ _ _ =>
        7 ∣ (2 ^ lab.n) ^ 2 - 1 ∧ ¬ GGTwE6BadLabel 7 lab) := by
      have hmark := ggInnerDiagOn_relabel hRig hInn (lab := ⟨.twD, 4, 3⟩)
        (by norm_num [LargeEvenInLambda2]) htwD
      exact largeEvenMarking_mono (fun lab R _ I F θ hP => by
        rw [hP.1]
        refine ⟨by norm_num, ?_⟩
        rintro ⟨h1, -, -⟩
        exact absurd h1 (by decide)) hmark
    have hnsplit : ¬ LargeEvenMarking ↥K' (fun lab _ _ _ _ _ => GGNbrSplitLabel 7 lab) := by
      rintro ⟨-, lab, hlab2, hraw⟩
      have hhas : GGHasLabel lab (K' ⧸ Subgroup.center K') := by
        unfold GGHasLabel
        refine largeEvenRawDatum_mono ?_ hraw
        rintro R _ I F ⟨-, -, θ, hP⟩
        exact ⟨θ⟩
      have hsp : GGNbrSplitLabel 7 lab := by
        obtain ⟨R, _, I, F, -, -, θ, hP⟩ := largeEvenRawDatum_exists hraw
        exact hP
      have hiso : GGLabelIso lab ⟨.twD, 4, 3⟩ :=
        hRig lab ⟨.twD, 4, 3⟩ (K' ⧸ Subgroup.center K') hlab2
          (by norm_num [LargeEvenInLambda2]) hhas htwD
      have heq : lab = ⟨.twD, 4, 3⟩ := a11nr_ggLabelIso_twD43 hiso
      rw [heq] at hsp
      norm_num [GGNbrSplitLabel, LargeEvenUntwisted] at hsp
    exact hNS G 7 B Bs x L D J hctx.1 y' K' hnb hnsplit hmark2

end CFSG.StandardType.A11

end
