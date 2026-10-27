module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeLinDefs
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinDict
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinPLab
import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
import CFSG.LocalAnalysis.StandardType.GGFrameRouteE7Models
import CFSG.Assembly.GL83StatedBridge
import CFSG.GroupTheory.ABGLocalTools.SL2FieldAutInner
import CFSG.Certificates.CentralizerFinite

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

private theorem finite_of_perfect_of_finite_centerQuotient {G : Type} [Group G]
    (hperf : commutator G = ⊤) (h : Finite (G ⧸ Subgroup.center G)) : Finite G := by
  haveI hfi : (Subgroup.center G).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  haveI hcs : Finite (commutatorSet G) :=
    CFSG.Certificates.finite_commutatorSet_of_finiteIndex_center
  haveI hcomm : Finite ↥(commutator G) :=
    Subgroup.instFiniteSubtypeMemCommutatorOfElemCommutatorSet G
  haveI htop : Finite ↥(⊤ : Subgroup G) := by simpa [hperf] using hcomm
  exact Finite.of_injective (Subgroup.topEquiv.symm : G → ↥(⊤ : Subgroup G))
    Subgroup.topEquiv.symm.injective

private theorem canonLabel_g2 (r n : ℕ) :
    CFSG.LocalAnalysis.GLTheoremA.canonLabel (⟨.G2, r, n⟩ : CFSG.Open.GLALabel) =
      ⟨.G2, r, n⟩ := rfl

private theorem canonLabel_g2der (r n : ℕ) :
    CFSG.LocalAnalysis.GLTheoremA.canonLabel (⟨.G2der, r, n⟩ : CFSG.Open.GLALabel) =
      ⟨.G2, 0, 1⟩ := rfl

section Certificates

theorem linJNoG2_holds :
    ∀ (J : Type) [Group J] (m : ℕ) (E : Type) [Field E] [Finite E], CharP E 2 → LinJ J m E →
      ¬ LargeEvenMarking J (fun lab _ _ _ _ _ => GGLabelG2 lab) := by
  intro J _ m E _ _ hchar hLin hmark
  rcases hLin with ⟨hm2, -, ⟨φ⟩⟩
  have hc : commutator J = ⊤ := hmark.1
  obtain ⟨lab, hG2, hmarkLab⟩ := CFSG.StandardType.FrameRoute.exists_glaLabel hmark
  haveI hQfin : Finite (J ⧸ Subgroup.center J) :=
    Finite.of_injective (φ : J ⧸ Subgroup.center J → PSLg m E) φ.injective
  haveI hJfin : Finite J := finite_of_perfect_of_finite_centerQuotient hc hQfin
  obtain ⟨f, _, hcard⟩ := CFSG.ABGLocalTools.card_eq_ringChar_pow (F := E)
  have hring : ringChar E = 2 := ringChar.eq E 2
  have hE : Nat.card E = 2 ^ f := by rw [hcard, hring]
  have hSL : LargeEvenSLGroup (Fin m) E = CFSG.Open.StatedSL m E :=
    CFSG.Assembly.largeEvenSLGroup_eq_statedSL m
  obtain ⟨ψ⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.largeEvenProj_equiv_statedProj (a := m) hSL
  have hφ : Nonempty (J ⧸ Subgroup.center J ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSL m E)) := ⟨φ.trans ψ⟩
  have hcanon := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.linLabelDict_of_ggLabelRigidInput
    CFSG.StandardType.ggLabelRigidInput_holds J lab m f E hm2 hE hmarkLab hφ
  obtain ⟨tg, r, n⟩ := lab
  change tg = .G2 ∨ tg = .G2der at hG2
  rcases hG2 with htg | htg
  · subst htg
    rw [canonLabel_g2 r n] at hcanon
    exact absurd (show (LargeEvenLieTag.G2 : LargeEvenLieTag) = .A from
      congrArg LargeEvenLabel.tag hcanon) (by decide)
  · subst htg
    rw [canonLabel_g2der r n] at hcanon
    exact absurd (show (LargeEvenLieTag.G2 : LargeEvenLieTag) = .A from
      congrArg LargeEvenLabel.tag hcanon) (by decide)

end Certificates

end CFSG.StandardType.TablePThreeKG

end
