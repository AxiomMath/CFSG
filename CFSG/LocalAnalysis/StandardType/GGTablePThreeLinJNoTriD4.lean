module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinDefs

import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPLab
import CFSG.Assembly.GL83StatedBridge
import CFSG.LocalAnalysis.StandardType.GGFrameRouteE7Models
import CFSG.LieType.Simplicity.LieModelFinite
import CFSG.RankThree.PerfectCover.HopfCentralCoversUnrestricted
import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTagsBasic

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

section Certificates

open CFSG.Open

theorem linJNoTriD4_holds :
    ∀ (J : Type) [Group J] (m : ℕ) (E : Type) [Field E] [Finite E], CharP E 2 → LinJ J m E →
      ¬ LargeEvenMarking J (fun lab _ _ _ _ _ => lab.tag = .triD4) := by
  intro J _ m E _ _ hchar hJ hmark
  haveI : CharP E 2 := hchar
  obtain ⟨lab, htag, hlab0⟩ := CFSG.StandardType.FrameRoute.exists_glaLabel hmark
  have hlab : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel J (fun l : GLALabel => l = lab) :=
    hlab0
  obtain ⟨-, hsimple, -⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.ggHasLabel_of_hasLabel hlab
  obtain ⟨labm, -, hdata⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_exists_markedModel hmark
  obtain ⟨R, hRgrp, I, F, θ, hdata'⟩ := hdata
  have hna : ∃ a b : R, a * b ≠ b * a := hdata'.2.1
  have hm : MarkedModel labm R := hdata'.2.2.2
  haveI hR : Finite R := CFSG.LieType.Simplicity.finite_of_native_lieModel hm
  have hnaJ : ∃ a b : J ⧸ Subgroup.center J, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hna
    exact ⟨θ.symm a, θ.symm b, fun h => hab (by
      have := congrArg θ h
      simpa using this)⟩
  haveI : Finite J :=
    CFSG.RankThree.PerfectCover.finite_of_quasisimple_finite_central_quotient
      (X := R) ⟨⟨hmark.1⟩, hsimple, hnaJ⟩ θ
  obtain ⟨k, -, hk⟩ := CFSG.StandardType.LayerExcThree.exists_card_eq_two_pow (D := E)
  have hiso : Nonempty (J ⧸ Subgroup.center J ≃* StatedProj (StatedSL m E)) := by
    obtain ⟨e⟩ := hJ.2.2
    obtain ⟨φ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.largeEvenProj_equiv_statedProj
      (a := m) (E := E) (H := LargeEvenSLGroup (Fin m) E)
      (CFSG.Assembly.largeEvenSLGroup_eq_statedSL m)
    exact ⟨e.trans φ⟩
  have hcanon := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.linLabelDict_holds
    J lab m k E hJ.1 hk hlab hiso
  have hself : CFSG.LocalAnalysis.GLTheoremA.canonLabel lab = lab := by
    obtain ⟨t, r, n⟩ := lab
    cases htag
    rfl
  rw [hself] at hcanon
  have hlabA : lab.tag = .A := by rw [hcanon]
  exact absurd (htag ▸ hlabA) (by decide)

end Certificates

end CFSG.StandardType.TablePThreeKG

end
