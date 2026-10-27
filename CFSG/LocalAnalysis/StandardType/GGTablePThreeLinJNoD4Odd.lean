module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinDefs
import CFSG.Assembly.GL83StatedBridge
import CFSG.GroupTheory.ABGLocalTools.SL2FieldAutInner
import CFSG.LocalAnalysis.GLTheoremA.CatA.K144IOut
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPLab
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Label
import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.RankThree.PartOne.S11d.Common
import CFSG.RankThree.PerfectCover.HopfCentralCoversUnrestricted
import CFSG.LocalAnalysis.GLTheoremA.CatA.K144IInn

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

section Certificates

theorem linJNoD4Odd_holds :
    ∀ (J : Type) [Group J] (m : ℕ) (E : Type) [Field E] [Finite E], CharP E 2 → LinJ J m E →
      ¬ LargeEvenMarking J (fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 4 ∧ Odd lab.n) := by
  intro J _ m E _ _ hchar hLin hmark
  obtain ⟨hm, -, he⟩ := hLin
  obtain ⟨e⟩ := he
  obtain ⟨hc, lab, hlab, hraw⟩ := hmark
  obtain ⟨R, hR, I, F, hQ⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨hRsimple, -, θ, hP⟩ := hQ
  obtain ⟨htag, hrank, -⟩ := hP
  haveI : IsSimpleGroup R := hRsimple
  haveI : IsSimpleGroup (J ⧸ Subgroup.center J) := MulEquiv.isSimpleGroup θ
  have hquis : CFSG.IsQuasisimple J :=
    CFSG.RankThree.PartOne.S11d.isQuasisimple_of_perfect_of_simple ⟨hc⟩ inferInstance
  have hraw' : CFSG.Assembly.LargeEvenRawDatum lab
      (fun R _ _ _ => Nonempty (J ⧸ Subgroup.center J ≃* R)) :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_mono
      (fun R _ I F hq => ⟨hq.2.2.choose⟩) hraw
  have hHas : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel J
      (fun l : CFSG.Open.GLALabel => l = lab) :=
    CFSG.LocalAnalysis.GLTheoremA.Y10F.hasLabel_of_quasisimple_rawDatum hquis hlab hraw'
  haveI : Finite J :=
    CFSG.RankThree.PerfectCover.finite_of_quasisimple_finite_central_quotient hquis e
  obtain ⟨k, -, hk⟩ := CFSG.ABGLocalTools.card_eq_ringChar_pow (F := E)
  have hrc : ringChar E = 2 := ringChar.eq_iff.mpr hchar
  rw [hrc] at hk
  obtain ⟨projEquiv⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.largeEvenProj_equiv_statedProj
      (a := m) (E := E) (H := LargeEvenSLGroup (Fin m) E)
      (CFSG.Assembly.largeEvenSLGroup_eq_statedSL (K := E) m)
  have hc := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.linLabelDict_holds
    J lab m k E hm hk hHas ⟨e.trans projEquiv⟩
  have hself := CFSG.LocalAnalysis.GLTheoremA.K144I.canonLabel_of_tag_D_four htag hrank
  rw [hself] at hc
  rw [hc] at htag
  exact absurd htag (by intro h; cases h)

end Certificates

end CFSG.StandardType.TablePThreeKG

end
