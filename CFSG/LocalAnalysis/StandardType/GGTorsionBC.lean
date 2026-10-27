module

public import CFSG.LocalAnalysis.StandardType.GGTorsionDefs
import CFSG.LocalAnalysis.StandardType.GGTorsionPSpComp
import CFSG.LocalAnalysis.StandardType.GGTorsionClassical
import CFSG.LocalAnalysis.StandardType.GGTorsionQuotComp
import CFSG.LocalAnalysis.StandardType.Marking

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section TorsionBC

private theorem tbc_center_eq_bot {R : Type} [Group R] (hs : IsSimpleGroup R)
    (hna : ∃ a b : R, a * b ≠ b * a) : Subgroup.center R = ⊥ := by
  haveI := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center R) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hna
    have ha : a ∈ Subgroup.center R := by rw [h]; exact Subgroup.mem_top a
    exact absurd (Subgroup.mem_center_iff.mp ha b).symm hab

theorem ggTorsionKnownOver_typeBC :
    GGTorsionKnownOver fun lab => lab.tag = .B ∨ lab.tag = .C := by
  intro p X _ _ hX δ J hdat hJ
  obtain ⟨hp, hp2, hδp, hδ1, hcomp, hmark⟩ := hdat
  obtain ⟨hXc, lab, hlab, hraw⟩ := hmark
  have htag : lab.tag = .B ∨ lab.tag = .C := by
    obtain ⟨R, _, I, F, -, -, θ, hP, -⟩ := largeEvenRawDatum_exists hraw
    exact hP
  obtain ⟨t, r, n⟩ := lab
  dsimp only at htag
  rcases htag with rfl | rfl
  all_goals
    obtain ⟨hn, hr1, hr2⟩ := hlab
    dsimp only [LargeEvenRawDatum] at hraw
    obtain ⟨K, _, _, hK, hs, hna, θ, -, hI⟩ := hraw
    have hδp' : ggInducedAut θ δ ^ p = 1 := by rw [← map_pow, hδp, map_one]
    have hJ' := ggTorsion_isComponentOf_image θ hcomp
    obtain ⟨e₂⟩ := ggTorsion_centerQuot_image_equiv θ hcomp.2.2.1
    have hZ := tbc_center_eq_bot hs hna
    have key := ggTorsion_psp_components (by omega) hn hK hZ hp hp2 hδp' hI hJ'
    refine ggTorsion_not_marking_of_classical ?_ hJ
    rcases key with ⟨t', n', f', hL⟩ | h360
    · exact Or.inl ⟨t', n', f', CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e₂.symm hL⟩
    · exact Or.inr (by rw [Nat.card_congr e₂.toEquiv]; exact h360)

end TorsionBC

end CFSG.StandardType
