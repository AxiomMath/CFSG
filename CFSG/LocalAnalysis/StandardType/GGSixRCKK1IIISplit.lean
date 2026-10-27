module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIISp
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType.RCKK1IIISp

open CFSG.Assembly CFSG.Blueprint CFSG.StandardType CFSG.StandardType.RCKC1
  CFSG.StandardType.LieOddCover

@[expose] def RCKRowK1IIISU :
    Prop :=
  ∀ (Jb : Type) [Group Jb] [Finite Jb], Odd (Nat.card (Subgroup.center Jb)) →
    LargeEvenMarking Jb (fun lab _ _ _ _ _ =>
      ggSixRCKLabelRow lab = .III ∧ (lab.tag = .twA ∨ lab.tag = .twD)) →
    ∃ (rb : Jb ⧸ Subgroup.center Jb) (Vb : Subgroup (Jb ⧸ Subgroup.center Jb)),
      RCKK1Data rb Vb ∧ RCKPosShort Jb rb Vb

private theorem rckIIISplit_tag {lab : LargeEvenLabel} (h : ggSixRCKLabelRow lab = .III) :
    (lab.tag = .B ∨ lab.tag = .C) ∨ (lab.tag = .twA ∨ lab.tag = .twD) := by
  obtain ⟨t, l, n⟩ := lab
  cases t <;> simp only [ggSixRCKLabelRow] at h <;>
    first
    | (simp; done)
    | exact absurd h (by decide)
    | (split_ifs at h <;> first | exact absurd h (by decide) | (simp_all; done))

theorem rckRowK1_III_of_su
    (hcov : GGLieOddCover) (hSU : RCKRowK1IIISU) : RCKRowK1 .III RCKPosShort := by
  intro Jb _ _ hodd hmark
  obtain ⟨hcomm, lab, hlab, hraw⟩ := hmark
  obtain ⟨R₀, _, I₀, F₀, hq₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ₀, hrow⟩ := hq₀
  rcases rckIIISplit_tag hrow with htag | htag
  · exact rckRowK1_III_sp hcov hodd ⟨hcomm, lab, hlab,
      largeEvenRawDatum_mono (fun R _ I F ⟨hs, hna, θ, hP⟩ => ⟨hs, hna, θ, hP, htag⟩) hraw⟩
  · exact hSU Jb hodd ⟨hcomm, lab, hlab,
      largeEvenRawDatum_mono (fun R _ I F ⟨hs, hna, θ, hP⟩ => ⟨hs, hna, θ, hP, htag⟩) hraw⟩

end CFSG.StandardType.RCKK1IIISp
