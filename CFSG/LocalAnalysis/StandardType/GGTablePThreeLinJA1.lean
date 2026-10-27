module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
import CFSG.Assembly.GL83StatedBridge
import CFSG.RankThree.PerfectCover.HopfCentralCoversUnrestricted
import CFSG.RankThree.PartOne.CTP.SeitzMaxSL2
import CFSG.RankThree.PartOne.CTP.SeitzLinear
import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
import CFSG.RankThree.PartOne.KC.LinearDegreeFive
import CFSG.RankThree.PartOne.KC.LinearEndpointStatements
import CFSG.RankThree.PartOne.KC.PlaneReductionGeneral

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

private theorem canonLabel_self_of_tag_A {lab : LargeEvenLabel} (h : lab.tag = .A) :
    CFSG.LocalAnalysis.GLTheoremA.canonLabel lab = lab := by
  rcases lab with ⟨tag, rank, n⟩
  dsimp only at h
  subst h
  rfl

section Certificates

theorem linJA1_holds :
    ∀ (J : Type) [Group J] (m : ℕ) (E : Type) [Field E] [Finite E], CharP E 2 → LinJ J m E →
      LargeEvenMarking J (fun lab _ _ _ _ _ => lab.tag = .A ∧ lab.rank = 1) → m = 2 := by
  intro J _ m E _ _ hchar hLinJ hmark
  obtain ⟨hcomm, lab, hlab2, hraw⟩ := hmark
  obtain ⟨R, hRgrp, I, F, hQ⟩ := CFSG.StandardType.Legacy.largeEvenRawDatum_exists hraw
  obtain ⟨hsimple, hnonab, θR, hP1⟩ := hQ
  obtain ⟨hAtag, hrank⟩ := hP1
  obtain ⟨φE⟩ := hLinJ.2.2
  have hnonabQ : ∃ a b : J ⧸ Subgroup.center J, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    refine ⟨θR.symm a, θR.symm b, fun h => hab ?_⟩
    have h1 := congrArg θR h
    simpa only [map_mul, θR.apply_symm_apply] using h1
  have hquasi : CFSG.IsQuasisimple J :=
    ⟨Group.IsPerfect.mk hcomm, (MulEquiv.isSimpleGroup_congr θR).2 hsimple, hnonabQ⟩
  haveI : Finite J :=
    CFSG.RankThree.PerfectCover.finite_of_quasisimple_finite_central_quotient hquasi φE
  have hHasLabel : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel J (fun l => l = lab) := by
    refine ⟨hcomm, lab, hlab2, ?_⟩
    simp only [CFSG.Open.GLARawDatum, CFSG.Assembly.LargeEvenRawDatum, hAtag]
    simp only [CFSG.Assembly.LargeEvenRawDatumLegacy, hAtag] at hraw
    obtain ⟨K, hKfield, hKfin, hKcard, hQ'⟩ := hraw
    refine ⟨K, hKfield, hKfin, hKcard, ?_⟩
    obtain ⟨hsimpleR, hnonabR, θ, _⟩ := hQ'
    exact ⟨hsimpleR, hnonabR, θ, trivial⟩
  have hφStated : Nonempty (J ⧸ Subgroup.center J ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSL m E)) := by
    refine ⟨?_⟩
    rw [← CFSG.Assembly.largeEvenSLGroup_eq_statedSL m]
    exact φE
  haveI : CharP E 2 := hchar
  obtain ⟨k, _hk, hcardE⟩ := CFSG.RankThree.PartOne.CTP.exists_card_eq_two_pow E
  have hcanon := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.linLabelDict_holds
    J lab m k E hLinJ.1 hcardE hHasLabel hφStated
  have hself : CFSG.LocalAnalysis.GLTheoremA.canonLabel lab = lab :=
    canonLabel_self_of_tag_A hAtag
  have hlab_eq : lab = ⟨.A, m - 1, k⟩ := by
    rw [← hself]
    exact hcanon
  have hrank' : lab.rank = m - 1 := by
    simpa using congrArg LargeEvenLabel.rank hlab_eq
  omega

end Certificates

end CFSG.StandardType.TablePThreeKG

end
