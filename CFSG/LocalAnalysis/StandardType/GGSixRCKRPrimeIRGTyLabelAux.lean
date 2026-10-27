module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGDefs
public import CFSG.ClassicalInvolution.ModelFacts.ClauseZero
public import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTQuot

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag StatedLieAdmissible)

theorem irg_lieModel_quot
    {X : Type} [Group X] {J : Subgroup X} {t : StatedLieTag} {n g : ℕ} (ht : GGPosTag t)
    (hadm : StatedLieAdmissible t n 2 g) (φ : (ggU t n g).K →* X) (hr : φ.range = J)
    (hk : φ.ker ≤ Subgroup.center (ggU t n g).K) :
    CFSG.Blueprint.LieModel (↥J ⧸ Subgroup.center ↥J) t n 2 g := by
  have hFT : CFSG.ClassicalInvolution.Generic.IsFundTag t := by
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
  have h0 := CFSG.ClassicalInvolution.ModelFacts.modelClauseZero t n 2 g Nat.prime_two hFT hadm
  have h1 : CFSG.Open.IsQuasisimple (ggU t n g).K ∧
      CFSG.Blueprint.LieModel ((ggU t n g).K ⧸ Subgroup.center (ggU t n g).K) t n 2 g := by
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact h0
  obtain ⟨hq, hM⟩ := h1
  subst hr
  obtain ⟨e⟩ := CFSG.LocalAnalysis.GLTheoremA.HSubT.quotCenter_mulEquiv_of_surj hq
    φ.rangeRestrict (MonoidHom.rangeRestrict_surjective φ) (fun x hx => hk
      (MonoidHom.mem_ker.mpr (congrArg Subtype.val hx)))
  exact CFSG.Blueprint.LieModel.of_mulEquiv e hM

end CFSG.StandardType.RCKRP
