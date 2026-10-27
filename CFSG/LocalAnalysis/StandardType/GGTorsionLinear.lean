module

public import CFSG.LocalAnalysis.StandardType.GGTorsionPSLComp
public import CFSG.LocalAnalysis.StandardType.GGTorsionNoPSL
public import CFSG.LocalAnalysis.StandardType.GGTorsionQuotComp
import CFSG.LocalAnalysis.StandardType.Marking

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section TorsionLinear

private theorem tl_center_eq_bot {R : Type} [Group R] (hs : IsSimpleGroup R)
    (hna : ∃ a b : R, a * b ≠ b * a) : Subgroup.center R = ⊥ := by
  haveI := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center R) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hna
    have ha : a ∈ Subgroup.center R := by rw [h]; exact Subgroup.mem_top a
    exact absurd (Subgroup.mem_center_iff.mp ha b).symm hab

theorem ggTorsionKnownOver_typeA :
    GGTorsionKnownOver fun lab => lab.tag = .A := by
  intro p X _ _ hX δ J hdat hJ
  obtain ⟨hp, hp2, hδp, hδ1, hcomp, hmark⟩ := hdat
  obtain ⟨hXc, lab, hlab, hraw⟩ := hmark
  have htag : lab.tag = .A := by
    obtain ⟨R, _, I, F, -, -, θ, hP, -⟩ := largeEvenRawDatum_exists hraw
    exact hP
  obtain ⟨t, r, n⟩ := lab
  obtain rfl : t = .A := htag
  obtain ⟨-, hr1, hr2⟩ := hlab
  dsimp only [LargeEvenRawDatum] at hraw
  obtain ⟨F, _, _, hF, hs, hna, θ, -, hI⟩ := hraw
  have hδp' : ggInducedAut θ δ ^ p = 1 := by rw [← map_pow, hδp, map_one]
  have hJ' := ggTorsion_isComponentOf_image θ hcomp
  obtain ⟨d, D, _, _, hd, hD2, -, ⟨e₁⟩⟩ :=
    ggTorsion_psl_components (m := r) (n := n) hF (tl_center_eq_bot hs hna) hp hp2 hδp' hI hJ'
  obtain ⟨e₂⟩ := ggTorsion_centerQuot_image_equiv θ hcomp.2.2.1
  haveI := hD2
  exact ggTorsion_not_marking_psl hd (e₂.trans e₁) hJ

end TorsionLinear

end CFSG.StandardType
