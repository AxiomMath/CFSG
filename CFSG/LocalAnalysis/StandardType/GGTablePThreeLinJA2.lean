module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinDefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPLab
import CFSG.RankThree.PerfectCover.HopfCentralCoversUnrestricted
import CFSG.Assembly.GL83StatedBridge
import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerTagsBasic

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

section Certificates

theorem linJA2_holds :
    ∀ (J : Type) [Group J] (m : ℕ) (E : Type) [Field E] [Finite E], CharP E 2 → LinJ J m E →
      LargeEvenMarking J (fun lab _ _ _ _ _ => GGLabelA2 lab ∧ lab.tag = .A) →
        m = 3 ∧ 4 ≤ Nat.card E := by
  intro J _ m E _ _ hchar hLinJ hmark
  obtain ⟨hm2, -, he⟩ := hLinJ
  obtain ⟨hcomm, lab, hlab, hraw⟩ := hmark
  have hrawC : CFSG.Assembly.LargeEvenRawDatum lab
      (fun R _ I F => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : J ⧸ Subgroup.center J ≃* R, GGLabelA2 lab ∧ lab.tag = .A) :=
    CFSG.Assembly.largeEvenRawDatumLegacy_to_canonical_carrier hraw
  obtain ⟨R, _, I, F, hsimple, hnonab, θ, hP⟩ :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_exists hrawC
  have hA2 : GGLabelA2 lab := hP.1
  have htagA : lab.tag = .A := hP.2
  have hrank : lab.rank = 2 := hA2.1
  have hn2 : 2 ≤ lab.n := hA2.2.1
  have hHas : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel J
      (fun l : CFSG.Open.GLALabel => l = lab) :=
    ⟨hcomm, lab, hlab, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
      (fun R' _ I' F' ⟨hs', hna', θ', _⟩ => ⟨hs', hna', θ', rfl⟩) hrawC⟩
  have hsimpleQ : IsSimpleGroup (J ⧸ Subgroup.center J) := by
    haveI := hsimple
    exact θ.isSimpleGroup
  have hnonabQ : ∃ a b : J ⧸ Subgroup.center J, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    exact ⟨θ.symm a, θ.symm b, fun h => hab (by
      have := congrArg θ h
      simpa [map_mul] using this)⟩
  have hIsQ : CFSG.IsQuasisimple J :=
    ⟨Group.IsPerfect.mk hcomm, hsimpleQ, hnonabQ⟩
  obtain ⟨e⟩ := he
  haveI : Finite (PSLg m E) := inferInstance
  haveI : Finite J :=
    CFSG.RankThree.PerfectCover.finite_of_quasisimple_finite_central_quotient hIsQ e
  haveI : CharP E 2 := hchar
  obtain ⟨k, -, hEk⟩ := CFSG.StandardType.LayerExcThree.exists_card_eq_two_pow E
  have he' : Nonempty (J ⧸ Subgroup.center J ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSL m E)) := by
    obtain ⟨ψ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.largeEvenProj_equiv_statedProj
      (H := CFSG.Assembly.LargeEvenSLGroup (Fin m) E)
      (CFSG.Assembly.largeEvenSLGroup_eq_statedSL (K := E) m)
    exact ⟨e.trans ψ⟩
  have hdict : CFSG.LocalAnalysis.GLTheoremA.canonLabel lab = ⟨.A, m - 1, k⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.linLabelDict_holds J lab m k E hm2 hEk hHas he'
  have hlab_eq : lab = ⟨.A, 2, lab.n⟩ := by
    rcases lab with ⟨t, r, n⟩
    change t = LargeEvenLieTag.A at htagA
    change r = 2 at hrank
    cases htagA
    cases hrank
    rfl
  have hcanonA : CFSG.LocalAnalysis.GLTheoremA.canonLabel lab = lab := by
    rw [hlab_eq]
    rfl
  have hEq : (⟨.A, 2, lab.n⟩ : LargeEvenLabel) = ⟨.A, m - 1, k⟩ := by
    rw [← hlab_eq]
    exact hcanonA.symm.trans hdict
  have hm1 : m - 1 = 2 := by
    have := congrArg LargeEvenLabel.rank hEq
    simpa using this.symm
  have hk : k = lab.n := by
    have := congrArg LargeEvenLabel.n hEq
    simpa using this.symm
  refine ⟨?_, ?_⟩
  · omega
  · rw [hEk, hk]
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) hn2

end Certificates

end CFSG.StandardType.TablePThreeKG

end
