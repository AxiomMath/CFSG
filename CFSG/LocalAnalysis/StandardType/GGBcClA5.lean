module

public import CFSG.LocalAnalysis.StandardType.GGBcDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNA8Seven
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGK1Final
public import CFSG.LocalAnalysis.StandardType.GGK1ScFinal
public import CFSG.LocalAnalysis.StandardType.GGTPNThmUKac
public import CFSG.LocalAnalysis.StandardType.GGMultTableCl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem bca5_inLambda2 : LargeEvenInLambda2 (⟨.A, 5, 2⟩ : LargeEvenLabel) := by
  simp [LargeEvenInLambda2]

private theorem bca5_generic : GGKacGenericCl (⟨.A, 5, 2⟩ : LargeEvenLabel) 5 := by
  unfold GGKacGenericCl
  norm_num

private theorem bca5_eq_of_labelIso_a52 {lab : LargeEvenLabel}
    (h : GGLabelIso lab (⟨.A, 5, 2⟩ : LargeEvenLabel)) : lab = ⟨.A, 5, 2⟩ := by
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

private theorem bca5_table_orbits_tag_A :
    ∀ D ∈ ggMultTableCl (.A 5) false 5 2, D.rZ ≤ 1 →
      ∀ o ∈ D.orbits, o.qs = true → o.lab.tag = .A := by
  decide

private theorem bca5_not_iso_of_tag_A {lab labJ : LargeEvenLabel} (hA : lab.tag = .A)
    (hBC : labJ.tag = .B ∨ labJ.tag = .C) (h : GGLabelIso lab labJ) : False := by
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h
  · rw [h] at hA
    rcases hBC with hb | hc
    · exact absurd (hA.symm.trans hb) (by decide)
    · exact absurd (hA.symm.trans hc) (by decide)
  · obtain ⟨h1, -⟩ := h
    rcases h1 with hb | hc
    · exact absurd (hA.symm.trans hb) (by decide)
    · exact absurd (hA.symm.trans hc) (by decide)
  · obtain ⟨h1, -⟩ := h
    have ht : lab.tag = .D := congrArg LargeEvenLabel.tag h1
    rw [hA] at ht
    exact absurd ht (by decide)
  · obtain ⟨-, h2⟩ := h
    have ht : labJ.tag = .D := congrArg LargeEvenLabel.tag h2
    rcases hBC with hb | hc
    · rw [ht] at hb; exact absurd hb (by decide)
    · rw [ht] at hc; exact absurd hc (by decide)
  · obtain ⟨h1, -⟩ := h
    have ht : lab.tag = .twD := congrArg LargeEvenLabel.tag h1
    rw [hA] at ht
    exact absurd ht (by decide)
  · obtain ⟨h1, -⟩ := h
    have ht : lab.tag = .twA := congrArg LargeEvenLabel.tag h1
    rw [hA] at ht
    exact absurd ht (by decide)
  · obtain ⟨h1, -⟩ := h
    have ht : lab.tag = .twD := congrArg LargeEvenLabel.tag h1
    rw [hA] at ht
    exact absurd ht (by decide)
  · obtain ⟨h1, -⟩ := h
    have ht : labJ.tag = .twD := congrArg LargeEvenLabel.tag h1
    rcases hBC with hb | hc
    · rw [ht] at hb; exact absurd hb (by decide)
    · rw [ht] at hc; exact absurd hc (by decide)

theorem ggBcClA5RK_holds :
    GGBcClA5RK := by
  intro p hp hp2 X _ _ A Ab σ J n hd hk labJ labX hΛJ hΛX hr hhJ hhX
  have hp5 : p = 5 := hr.2.1
  have hlabXeq : labX = (⟨.A, 5, 2⟩ : LargeEvenLabel) := hr.2.2
  subst hp5
  subst hlabXeq
  obtain ⟨⟨hloc, hflat, hcardAb, hrankb, hnum, hself, honly, hmark⟩, hcor⟩ := hd
  have hBC : labJ.tag = .B ∨ labJ.tag = .C := hr.1.1
  have hrig := ggLabelRigidInput_holds
  have hgen : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
      GGHasLabel lab (X ⧸ Subgroup.center X) → GGKacGenericCl lab 5 := by
    intro lab hlab hhas
    have hiso := hrig lab (⟨.A, 5, 2⟩ : LargeEvenLabel) (X ⧸ Subgroup.center X) hlab
      bca5_inLambda2 hhas hhX
    rw [bca5_eq_of_labelIso_a52 hiso]
    exact bca5_generic
  have hK0 : GGK0Main GGKacGenericCl GGMultValidCl := ggK0Main_cl_of_schur ggK0Schur_cl
  obtain ⟨lab, hlabIn, -, -, hhasLab, D, hValid, hrZ, -, hlabJ, hlast⟩ :=
    exists_ggKacDatum_of_ggK0Main hK0 ggK0Schur_cl hloc hself hk honly hmark hgen
  have hlab_eq : lab = (⟨.A, 5, 2⟩ : LargeEvenLabel) :=
    bca5_eq_of_labelIso_a52 (hrig lab (⟨.A, 5, 2⟩ : LargeEvenLabel) (X ⧸ Subgroup.center X)
      hlabIn bca5_inLambda2 hhasLab hhX)
  have hDmem : D ∈ ggMultTableCl (.A 5) false 5 2 := by
    obtain ⟨T, tw, m, hT, hmem⟩ := hValid
    rw [hlab_eq] at hT
    simp only [ggKacTypeClOfLabel] at hT
    injection hT with hT
    obtain ⟨rfl, rfl, rfl⟩ := hT
    exact hmem
  obtain ⟨o, ho, hqs, -, hΛo⟩ := hlast
  have hhaso : GGHasLabel o.lab (J ⧸ Subgroup.center J) := hlabJ o ho hqs
  have hisoo : GGLabelIso o.lab labJ :=
    hrig o.lab labJ (J ⧸ Subgroup.center J) hΛo hΛJ hhaso hhJ
  have htagA : o.lab.tag = .A := bca5_table_orbits_tag_A D hDmem hrZ o ho hqs
  exact (bca5_not_iso_of_tag_A htagA hBC hisoo).elim

end CFSG.StandardType

end
