module

public import CFSG.LocalAnalysis.StandardType.GGLieCoreA3Defs
public import CFSG.LocalAnalysis.StandardType.GGLieCoreToral
public import CFSG.LocalAnalysis.StandardType.GGLieCoreE6NonToral

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag)
open CFSG.StandardType.ExcFramesHalf (IsToralSubgroup)

theorem ggLieA3Alg_of_toral
    (hN : GGLieE6NonToralNoA8) (hT : GGLieA3AlgToral) : GGLieA3Alg := by
  intro t ht f hf A K hA hel hcard hK hJ
  have halg :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.isAlgebraic_zmod_algebraicClosure_of_finite (ZMod 2) 2
  by_cases hTor : IsToralSubgroup (langTag t) GGL A
  · exact hT t ht f hf A K hA hel hcard hTor hK hJ
  · rcases ht with rfl | rfl | rfl
    ·
      exfalso
      have hAd : A ≤ adjointGroup Tag.E6 GGL := hA.trans inf_le_left
      have hKd : K ≤ adjointGroup Tag.E6 GGL :=
        hK.1.trans (inf_le_left.trans
          ((Subgroup.commutator_le_self (ggFixGp .E6 f)).trans inf_le_left))
      have hKc := hK.1.trans inf_le_right
      have hperf : ⁅K, K⁆ = K :=
        CFSG.StandardType.LinSemisimple.commutator_eq_self_of_isQuasisimple hK.2.2
      have hLie : LieModel (↥K ⧸ Subgroup.center ↥K) .PSL 4 2 1 := hJ
      exact (hN GGL halg A hAd hel hcard hTor K hKd hKc hperf) hLie
    ·
      exfalso
      refine hTor (isToralSubgroup_of_card_le_sq (τ := Tag.F4) (L := GGL) halg (by norm_num)
        (by norm_num) (hA.trans inf_le_left)
        (Nat.finite_of_card_ne_zero (α := A) (by rw [hcard]; norm_num)) hel
        (le_of_eq hcard) ?_)
      intro h
      exact absurd h (by decide)
    ·
      exfalso
      have hAd : A ≤ adjointGroup Tag.E6 GGL := hA.trans inf_le_left
      have hKd : K ≤ adjointGroup Tag.E6 GGL :=
        hK.1.trans (inf_le_left.trans
          ((Subgroup.commutator_le_self (ggFixGp .twistedE6 f)).trans inf_le_left))
      have hKc := hK.1.trans inf_le_right
      have hperf : ⁅K, K⁆ = K :=
        CFSG.StandardType.LinSemisimple.commutator_eq_self_of_isQuasisimple hK.2.2
      have hLie : LieModel (↥K ⧸ Subgroup.center ↥K) .PSL 4 2 1 := hJ
      exact (hN GGL halg A hAd hel hcard hTor K hKd hKc hperf) hLie

end CFSG.StandardType.LieCore
