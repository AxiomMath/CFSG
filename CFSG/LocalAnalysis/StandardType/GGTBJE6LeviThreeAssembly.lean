module

public import CFSG.LocalAnalysis.StandardType.GGTBJE6LeviSplit
public import CFSG.LocalAnalysis.StandardType.GGTBJE6Rows
public import CFSG.LocalAnalysis.StandardType.GGTBJETypeCells
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflDom
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGRootGenExcLabels
import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreSix
import CFSG.LocalAnalysis.StandardType.GGTwistedF4DiagRaw
import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45ConfigIso
import CFSG.LocalAnalysis.StandardType.GGAssemblyFiveDefs
import CFSG.LocalAnalysis.StandardType.GGExclNoIso

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggTBJE6LeviL_three_of_TQ
    (hRig : GGLabelRigidInput)
    (hT : GGTBJETypeLeviL .E6 fun p n labJ =>
      ggTBJE6RowCand p n labJ ∨ ¬ (p = 3 ∧ 3 ∣ 2 ^ n - 1))
    (hQ : GGTBJETypeLeviL .E6 fun p n labJ => ggTBJE6RowCand p n labJ ∨ ¬ (p = 3 ∧ n = 1)) :
    GGTBJETypeLeviL .E6 fun p n labJ => ggTBJE6RowCand p n labJ ∨ p ≠ 3 := by
  intro G _ _ p B Bs x L D J y K hH _ hLd hX n hΛ hL hreg labJ hΛJ hJlab hdvd hnc
  have hp3 : p = 3 := by
    by_contra h
    exact hnc (Or.inr h)
  have hst : LargeEvenStandardType p B x L := hH.1.1.2.2.2.2.2.2.2
  obtain ⟨labs, hlabs, hhass, _, _, _, _, _, hPs⟩ := largeEvenMarking_exists_hasLabel hst.1
  have heq : labs = (⟨.E6, 0, n⟩ : LargeEvenLabel) :=
    eq_of_ggLabelIso_of_excTag (Or.inl rfl) (hRig ⟨.E6, 0, n⟩ labs _ hΛ hlabs hL hhass)
  have hs : LargeEvenSplit p (⟨.E6, 0, n⟩ : LargeEvenLabel) := heq ▸ hPs.1
  rcases hs with ⟨-, h⟩ | ⟨hu, -⟩ | ⟨ht, -⟩ | ⟨hn1, -⟩
  · exact hT G p B Bs x L D J y K hH hLd hX n hΛ hL hreg labJ hΛJ hJlab hdvd
      fun h' => Or.elim h' (fun hc => hnc (Or.inl hc)) fun hn => hn ⟨hp3, by rw [hp3] at h; exact h⟩
  · exact absurd trivial hu
  · simp at ht
  · exact hQ G p B Bs x L D J y K hH hLd hX n hΛ hL hreg labJ hΛJ hJlab hdvd
      fun h' => Or.elim h' (fun hc => hnc (Or.inl hc)) fun hn => hn ⟨hp3, hn1⟩

theorem ggTBJE6LeviK_three_of_TQ
    (hRig : GGLabelRigidInput)
    (hT : GGTBJETypeLeviK .E6 fun p n labJ =>
      ggTBJE6RowCand p n labJ ∨ ¬ (p = 3 ∧ 3 ∣ 2 ^ n - 1))
    (hQ : GGTBJETypeLeviK .E6 fun p n labJ => ggTBJE6RowCand p n labJ ∨ ¬ (p = 3 ∧ n = 1)) :
    GGTBJETypeLeviK .E6 fun p n labJ => ggTBJE6RowCand p n labJ ∨ p ≠ 3 := by
  intro G _ _ p B Bs x L D J y K hH hJK _ hLd hX n hΛ hK hreg labJ hΛJ hJlab hdvd hnc
  have hp3 : p = 3 := by
    by_contra h
    exact hnc (Or.inr h)
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hHS := ggNbr_halfSplit_of_hyp ggRawInnFieldInput_holds
    (ggRawInndiagIsoInput_of_rest (ggRawInndiagIsoRestInput_of_round5 ggRawInndiagIsoRound5_holds))
    hH.1 hnb (hH.2.2.1.2 y K hnb)
  obtain ⟨labh, hlabh, hhash, _, _, _, _, _, hHSlab⟩ := largeEvenMarking_exists_hasLabel hHS
  have heq : labh = (⟨.E6, 0, n⟩ : LargeEvenLabel) :=
    eq_of_ggLabelIso_of_excTag (Or.inl rfl) (hRig ⟨.E6, 0, n⟩ labh _ hΛ hlabh hK hhash)
  rw [heq] at hHSlab
  rcases NbrInnerMore.halfSplit_E6_cases hHSlab with h | ⟨hn1, -⟩ | ⟨-, hp7⟩
  · exact hT G p B Bs x L D J y K hH hJK hLd hX n hΛ hK hreg labJ hΛJ hJlab hdvd
      fun h' => Or.elim h' (fun hc => hnc (Or.inl hc)) fun hn => hn ⟨hp3, by rw [hp3] at h; exact h⟩
  · exact hQ G p B Bs x L D J y K hH hJK hLd hX n hΛ hK hreg labJ hΛJ hJlab hdvd
      fun h' => Or.elim h' (fun hc => hnc (Or.inl hc)) fun hn => hn ⟨hp3, hn1⟩
  · omega

theorem ggTBJE6LeviL_of_TQ
    (hRig : GGLabelRigidInput)
    (hT : GGTBJETypeLeviL .E6 fun p n labJ =>
      ggTBJE6RowCand p n labJ ∨ ¬ (p = 3 ∧ 3 ∣ 2 ^ n - 1))
    (hQ : GGTBJETypeLeviL .E6 fun p n labJ => ggTBJE6RowCand p n labJ ∨ ¬ (p = 3 ∧ n = 1)) :
    GGTBJE6LeviL :=
  ggTBJE6LeviL_of_three hRig (ggTBJE6LeviL_three_of_TQ hRig hT hQ)

theorem ggTBJE6LeviK_of_TQ
    (hRig : GGLabelRigidInput)
    (hT : GGTBJETypeLeviK .E6 fun p n labJ =>
      ggTBJE6RowCand p n labJ ∨ ¬ (p = 3 ∧ 3 ∣ 2 ^ n - 1))
    (hQ : GGTBJETypeLeviK .E6 fun p n labJ => ggTBJE6RowCand p n labJ ∨ ¬ (p = 3 ∧ n = 1)) :
    GGTBJE6LeviK :=
  ggTBJE6LeviK_of_three hRig (ggTBJE6LeviK_three_of_TQ hRig hT hQ)

end CFSG.StandardType

end
