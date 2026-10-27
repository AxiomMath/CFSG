module

public import CFSG.LocalAnalysis.StandardType.GGTorsionE67Known
public import CFSG.LocalAnalysis.StandardType.GGNbrLangS1ExcInputs
public import CFSG.LocalAnalysis.StandardType.GGTorsionDatum
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Q2ExceptionalRest

private theorem tag_nonE_of_ggLabelIso {lab lab' : LargeEvenLabel} (h : GGLabelIso lab lab')
    (hP : lab.tag ≠ .E8 ∧ lab.tag ≠ .E7 ∧ lab.tag ≠ .E6 ∧ lab.tag ≠ .twE6) :
    lab'.tag ≠ .E8 ∧ lab'.tag ≠ .E7 ∧ lab'.tag ≠ .E6 ∧ lab'.tag ≠ .twE6 := by
  obtain ⟨t, _, _⟩ := lab
  obtain ⟨t', _, _⟩ := lab'
  rcases h with h | h | h | h | h | h | h | h
  · have ht : t = t' := congrArg LargeEvenLabel.tag h
    rw [← ht]
    simpa using hP
  · obtain ⟨-, hB', -⟩ := h
    rcases hB' with hB' | hB' <;> rw [hB'] <;> simp
  · obtain ⟨-, h2⟩ := h
    have ht : t' = .A := congrArg LargeEvenLabel.tag h2
    rw [ht]; simp
  · obtain ⟨-, h2⟩ := h
    have ht : t' = .D := congrArg LargeEvenLabel.tag h2
    rw [ht]; simp
  · obtain ⟨-, h2⟩ := h
    have ht : t' = .twA := congrArg LargeEvenLabel.tag h2
    rw [ht]; simp
  · obtain ⟨-, h2⟩ := h
    have ht : t' = .twD := congrArg LargeEvenLabel.tag h2
    rw [ht]; simp
  · obtain ⟨-, h2⟩ := h
    have ht : t' = .A := congrArg LargeEvenLabel.tag h2
    rw [ht]; simp
  · obtain ⟨h1, -⟩ := h
    have ht : t' = .twD := congrArg LargeEvenLabel.tag h1
    rw [ht]; simp

theorem ggBstarToralJExcInputOn_nonE_holds
    : GGBstarToralJExcInputOn
      (fun lab => lab.tag ≠ .E8 ∧ lab.tag ≠ .E7 ∧ lab.tag ≠ .E6 ∧ lab.tag ≠ .twE6) := by
  intro G _ _ B Bs x L D J hcfg hm hJ labJ hΛJ htJ hlabelJ
  exfalso
  obtain ⟨hperfL, lab, hlab, hraw⟩ := hm
  obtain ⟨_, _, _, _, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, _, hS, -, -⟩ := hQ
  have hhas : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) := by
    unfold GGHasLabel
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨_, _, θ', -, -⟩
    exact ⟨θ'⟩
  obtain ⟨δ, hdat⟩ := exists_ggTorsionDatum hcfg.1 hcfg.2.2
  obtain ⟨hp, hp2, hδp, hδ1, hcomp, hmark'⟩ := hdat
  obtain ⟨-, lab', hlab', hraw'⟩ := hmark'
  have hhas' : GGHasLabel lab' (↥L ⧸ Subgroup.center ↥L) := by
    unfold GGHasLabel
    refine largeEvenRawDatum_mono ?_ hraw'
    rintro R _ I F ⟨_, _, θ', -, -⟩
    exact ⟨θ'⟩
  have hiso : GGLabelIso lab lab' :=
    ggLabelRigidInput_holds lab lab' _ hlab hlab' hhas hhas'
  have hS' : lab'.tag ≠ .E8 ∧ lab'.tag ≠ .E7 ∧ lab'.tag ≠ .E6 ∧ lab'.tag ≠ .twE6 :=
    tag_nonE_of_ggLabelIso hiso hS
  have hdat' : GGTorsionDatum
      (fun lab => lab.tag ≠ .E8 ∧ lab.tag ≠ .E7 ∧ lab.tag ≠ .E6 ∧ lab.tag ≠ .twE6)
      3 δ (J.subgroupOf L) := by
    refine ⟨hp, hp2, hδp, hδ1, hcomp, ?_⟩
    refine ⟨hperfL, lab', hlab', ?_⟩
    refine largeEvenRawDatum_mono ?_ hraw'
    rintro R _ I F ⟨hs, hna, θ', -, hθ'⟩
    exact ⟨hs, hna, θ', hS', hθ'⟩
  have hnot : ¬ LargeEvenMarking ↥(J.subgroupOf L)
      (fun lab _ _ _ _ _ => lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7) :=
    ggTorsionKnownOverTags_nonE 3 (↥L) hperfL δ (J.subgroupOf L) hdat'
  have hJL : J ≤ L := hcfg.2.2.1.2.2.2.2.2.1.1.trans inf_le_left
  have hJM := ggInnerDiagOn_relabel ggLabelRigidInput_holds (lab := labJ) hJ hΛJ hlabelJ
  have hJM' : LargeEvenMarking ↥J
      (fun lab _ _ _ _ _ => lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7) := by
    refine largeEvenMarking_mono ?_ hJM
    intro lab _ _ _ _ _ h
    exact h.1.symm ▸ htJ
  have hJmark : LargeEvenMarking ↥(J.subgroupOf L)
      (fun lab _ _ _ _ _ => lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7) :=
    largeEvenMarking_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJL) hJM'
  exact (hnot hJmark).elim

end Q2ExceptionalRest

end CFSG.StandardType
