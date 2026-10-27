module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinDefs
import CFSG.LocalAnalysis.StandardType.GGFrameRouteE7Models
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnExcLabel
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Label
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPLab
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPieces
import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
import CFSG.Assembly.GL83StatedBridge
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.RankThree.PartOne.CTP.SeitzMaxSL2

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

private theorem canonLabel_eq_self_of_twA {lab : LargeEvenLabel} (ht : lab.tag = .twA) :
    CFSG.LocalAnalysis.GLTheoremA.canonLabel lab = lab := by
  obtain ⟨t, r, n⟩ := lab
  subst ht
  rfl

private theorem canonLabel_eq_self_of_A (r n : ℕ) :
    CFSG.LocalAnalysis.GLTheoremA.canonLabel (⟨.A, r, n⟩ : LargeEvenLabel) = ⟨.A, r, n⟩ := rfl

private theorem false_of_canonLabel_twA {lab : LargeEvenLabel} {a e : ℕ}
    (h : CFSG.LocalAnalysis.GLTheoremA.canonLabel lab = ⟨.A, a, e⟩) (ht : lab.tag = .twA) :
    False := by
  rw [canonLabel_eq_self_of_twA ht] at h
  have htag : lab.tag = .A := by rw [h]
  have hbad : (.twA : LargeEvenLieTag) = .A := by rw [← ht, htag]
  exact nomatch hbad

section LinJNoTwA2Proof

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA

theorem linJNoTwA2_holds :
    ∀ (J : Type) [Group J] (m : ℕ) (E : Type) [Field E] [Finite E], CharP E 2 → LinJ J m E →
      ¬ LargeEvenMarking J (fun lab _ _ _ _ _ => GGLabelA2 lab ∧ lab.tag = .twA) := by
  intro J _ m E _ _ hchar hLin hmark
  obtain ⟨hm, -, ⟨φ⟩⟩ := hLin
  obtain ⟨lab, hPlab, hHas⟩ := CFSG.StandardType.FrameRoute.exists_glaLabel hmark
  obtain ⟨-, htag⟩ := hPlab
  obtain ⟨hcomm, -, -, R, instR, -, -, θ, hRsimple, hnonab, -⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_exists hHas
  letI := instR
  haveI : IsSimpleGroup R := hRsimple
  have hJZsimple : IsSimpleGroup (J ⧸ Subgroup.center J) := MulEquiv.isSimpleGroup θ
  haveI : IsSimpleGroup (J ⧸ Subgroup.center J) := hJZsimple
  obtain ⟨k, -, hEcard⟩ := CFSG.RankThree.PartOne.CTP.exists_card_eq_two_pow E
  obtain ⟨ψ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.largeEvenProj_equiv_statedProj
    (a := m) (E := E) (CFSG.Assembly.largeEvenSLGroup_eq_statedSL m)
  have hiso : J ⧸ Subgroup.center J ≃* StatedProj (StatedSL m E) := φ.trans ψ
  have hModel : StatedClassicalModel (J ⧸ Subgroup.center J) .PSL m 2 k :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.statedClassicalModel_psl_of_isSimpleGroup
      hm hEcard hiso
  have hModel' : StatedClassicalModel (J ⧸ Subgroup.center J) .PSL ((m - 1) + 1) 2 k := by
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ m)]
  have hJperf : Group.IsPerfect J := Group.IsPerfect.mk hcomm
  obtain ⟨a, b, hab⟩ := hnonab
  have hJqs : IsQuasisimple J :=
    ⟨hJperf, hJZsimple, θ.symm a, θ.symm b, fun h => hab (by simpa using congrArg θ h)⟩
  have hHasA : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel J
      (fun l => l = ⟨.A, m - 1, k⟩) :=
    CFSG.LocalAnalysis.GLTheoremA.Y10F.hasLabel_of_statedClassicalModel_PSL hJqs hModel'
  have hcanon := CFSG.LocalAnalysis.GLTheoremA.Y10GInnExcLabel.canonLabel_eq_of_hasLabel
    CFSG.StandardType.ggLabelRigidInput_holds hHas hHasA
  have hcanon' : CFSG.LocalAnalysis.GLTheoremA.canonLabel lab = ⟨.A, m - 1, k⟩ := by
    rw [canonLabel_eq_self_of_A (m - 1) k] at hcanon
    exact hcanon
  exact false_of_canonLabel_twA hcanon' htag

end LinJNoTwA2Proof

end CFSG.StandardType.TablePThreeKG

end
