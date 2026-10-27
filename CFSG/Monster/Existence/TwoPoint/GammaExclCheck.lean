
module

public import CFSG.Monster.Existence.TwoPoint.GammaExclCheckBase

public import CFSG.Monster.Existence.TwoPoint.GammaExclDef

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.Monster.B CFSG.Monster.B.Short

theorem xHat_mem_GmatM
    (j : ℕ) : xHat j ∈ GmatM := by
  rw [xHat_eq_prod]
  refine Subgroup.list_prod_mem _ fun g hg => ?_
  obtain ⟨k, _, rfl⟩ := List.mem_map.1 hg
  exact gxElem_mem_GmatM k

theorem gxD_conj :
    gxD * tGriess * gxD⁻¹ = fiAlpha := fi_conj_alpha

theorem gx_conj_deltaHat
    (j : ℕ) :
    (xHat j * gxD) * tGriess * (xHat j * gxD)⁻¹ = deltaHat j := by
  unfold deltaHat
  rw [← gxD_conj]
  group

theorem gx_fix_axis
    {j : ℕ} {g : MGriess} (hg : g ∈ GmatM) (h : g * deltaHat j = deltaHat j * g) :
    g.1 (gxAxis j) = gxAxis j := by
  have hy : xHat j * gxD ∈ GmatM := mul_mem (xHat_mem_GmatM j) (fiMkW_mem_GmatM _)
  rw [← gx_conj_deltaHat] at h
  exact gx_fix_of_commute (Subgroup.mem_comap.1 hy) (Subgroup.mem_comap.1 hg)
    (congrArg Subtype.val h)

theorem gxAxis_eq
    (j : ℕ) : gxAxis j = wordLin (gxYWord j) aStar := by
  have e : fiMkW (fiCAlpha ++ gxProdWord (gxXList j)) = xHat j * gxD := by
    rw [fiMkW_append, fiMkW_gxProdWord, xHat_eq_prod]
    rfl
  unfold gxAxis gxYWord
  rw [← e]
  rfl

theorem gxNodeCheck_sound
    {j : ℕ} (h : gxNodeNe j) :
    (j ≠ 9 → deltaHat j * fiAlpha ≠ fiAlpha * deltaHat j) ∧
      deltaHat j * betaPrime ≠ betaPrime * deltaHat j := by
  have hu := gxAxis_eq j
  refine ⟨fun hj hc => h.1 hj ?_, fun hc => h.2 ?_⟩
  · have hf := gx_fix_axis (fiMkW_mem_GmatM _) hc.symm
    have e : wordLin (gxYWord j ++ fiWAlpha) aStar = fiAlpha.1 (wordLin (gxYWord j) aStar) := by
      rw [wordLin_append]
      rfl
    rw [e, ← hu]
    exact hf
  · have hmem : betaPrime ∈ GmatM := by
      rw [← fiMkW_wordBetaPrime]
      exact fiMkW_mem_GmatM _
    have hf := gx_fix_axis hmem hc.symm
    have e : wordLin (gxYWord j ++ gxBPWord) aStar = betaPrime.1 (wordLin (gxYWord j) aStar) := by
      rw [wordLin_append, ← fiMkW_wordBetaPrime]
      rfl
    rw [e, ← hu]
    exact hf

end CFSG.Monster.Existence
