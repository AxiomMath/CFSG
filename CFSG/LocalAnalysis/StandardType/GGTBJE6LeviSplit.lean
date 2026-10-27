module

public import CFSG.LocalAnalysis.StandardType.GGTBJE6LeviCell
public import CFSG.LocalAnalysis.StandardType.GGTBJETypeCells
public import Certificates.Certificate2261
public import Certificates.Certificate2262
public import Certificates.Certificate2263
public import Certificates.Certificate2264
public import Certificates.Certificate2265
public import Certificates.Certificate2266
public import Certificates.Certificate2267
public import Certificates.Certificate2268
public import Certificates.Certificate2269
public import Certificates.Certificate2270
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate8064
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

theorem GGTBJETypeLeviL.of_or {τ : LargeEvenLieTag} {C P : ℕ → ℕ → LargeEvenLabel → Prop}
    (h₁ : GGTBJETypeLeviL τ fun p n lab => C p n lab ∨ P p n lab)
    (h₂ : GGTBJETypeLeviL τ fun p n lab => C p n lab ∨ ¬ P p n lab) :
    GGTBJETypeLeviL τ C := by
  intro G _ _ p B Bs x L D J y K hH _ hL hX n hΛ hhas hreg labJ hΛJ hJlab hdvd hnc
  by_cases hP : P p n labJ
  · exact h₂ G p B Bs x L D J y K hH hL hX n hΛ hhas hreg labJ hΛJ hJlab hdvd
      fun h => Or.elim h hnc fun h' => h' hP
  · exact h₁ G p B Bs x L D J y K hH hL hX n hΛ hhas hreg labJ hΛJ hJlab hdvd
      fun h => Or.elim h hnc hP

theorem GGTBJETypeLeviK.of_or {τ : LargeEvenLieTag} {C P : ℕ → ℕ → LargeEvenLabel → Prop}
    (h₁ : GGTBJETypeLeviK τ fun p n lab => C p n lab ∨ P p n lab)
    (h₂ : GGTBJETypeLeviK τ fun p n lab => C p n lab ∨ ¬ P p n lab) :
    GGTBJETypeLeviK τ C := by
  intro G _ _ p B Bs x L D J y K hH hJK _ hK hX n hΛ hhas hreg labJ hΛJ hJlab hdvd hnc
  by_cases hP : P p n labJ
  · exact h₂ G p B Bs x L D J y K hH hJK hK hX n hΛ hhas hreg labJ hΛJ hJlab hdvd
      fun h => Or.elim h hnc fun h' => h' hP
  · exact h₁ G p B Bs x L D J y K hH hJK hK hX n hΛ hhas hreg labJ hΛJ hJlab hdvd
      fun h => Or.elim h hnc hP

theorem ggTBJE6LeviL_split
    (hRig : GGLabelRigidInput) :
    GGTBJETypeLeviL .E6 fun p n labJ => ggTBJE6RowCand p n labJ ∨ p = 3 := by
  intro G _ _ p B Bs x L D J y K hH _ _ _ n hΛ hL _ _ _ _ _ hnc
  have hp3 : p ≠ 3 := fun h => hnc (Or.inr h)
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hst : LargeEvenStandardType p B x L := hH.1.1.2.2.2.2.2.2.2
  obtain ⟨labs, hlabs, hhass, _, _, _, _, _, hPs⟩ := largeEvenMarking_exists_hasLabel hst.1
  have heq : labs = (⟨.E6, 0, n⟩ : LargeEvenLabel) :=
    eq_of_ggLabelIso_of_excTag (Or.inl rfl) (hRig ⟨.E6, 0, n⟩ labs _ hΛ hlabs hL hhass)
  have hs : LargeEvenSplit p (⟨.E6, 0, n⟩ : LargeEvenLabel) := heq ▸ hPs.1
  have hpn : p ∣ 2 ^ n - 1 := by
    rcases hs with ⟨-, h⟩ | ⟨hu, -⟩ | ⟨ht, -⟩ | ⟨-, h3⟩
    · exact h
    · exact absurd trivial hu
    · simp at ht
    · exact absurd h3 hp3
  exact ggTBJE6LeviL_of_coverModel hH hp3 (ggE6Split_coverModel_L hRig hH hΛ hL hpn hp3)

theorem ggTBJE6LeviK_split
    (hRig : GGLabelRigidInput) :
    GGTBJETypeLeviK .E6 fun p n labJ => ggTBJE6RowCand p n labJ ∨ p = 3 := by
  intro G _ _ p B Bs x L D J y K hH hJK _ _ _ n hΛ hK hreg _ _ _ _ hnc
  have hp3 : p ≠ 3 := fun h => hnc (Or.inr h)
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hHS := ggNbr_halfSplit_of_hyp ggRawInnFieldInput_holds
    (ggRawInndiagIsoInput_of_rest (ggRawInndiagIsoRestInput_of_round5 ggRawInndiagIsoRound5_holds))
    hH.1 hnb (hH.2.2.1.2 y K hnb)
  obtain ⟨labh, hlabh, hhash, _, _, _, _, _, hHSlab⟩ := largeEvenMarking_exists_hasLabel hHS
  have heq : labh = (⟨.E6, 0, n⟩ : LargeEvenLabel) :=
    eq_of_ggLabelIso_of_excTag (Or.inl rfl) (hRig ⟨.E6, 0, n⟩ labh _ hΛ hlabh hK hhash)
  rw [heq] at hHSlab
  have hpn : p ∣ 2 ^ n - 1 := by
    rcases NbrInnerMore.halfSplit_E6_cases hHSlab with h | ⟨-, h3⟩ | ⟨hn, hp7⟩
    · exact h
    · exact absurd h3 hp3
    · subst hn hp7
      rcases hreg with h | h <;> norm_num at h
  exact ggTBJE6LeviK_of_coverModel hH hJK hp3 (ggE6Split_coverModel_K hRig hH hΛ hK hpn hp3)

theorem ggTBJE6LeviL_of_three
    (hRig : GGLabelRigidInput)
    (h3 : GGTBJETypeLeviL .E6 fun p n labJ => ggTBJE6RowCand p n labJ ∨ p ≠ 3) :
    GGTBJE6LeviL :=
  GGTBJETypeLeviL.of_or (P := fun p _ _ => p = 3) (ggTBJE6LeviL_split hRig) h3

theorem ggTBJE6LeviK_of_three
    (hRig : GGLabelRigidInput)
    (h3 : GGTBJETypeLeviK .E6 fun p n labJ => ggTBJE6RowCand p n labJ ∨ p ≠ 3) :
    GGTBJE6LeviK :=
  GGTBJETypeLeviK.of_or (P := fun p _ _ => p = 3) (ggTBJE6LeviK_split hRig) h3

end CFSG.StandardType

end
