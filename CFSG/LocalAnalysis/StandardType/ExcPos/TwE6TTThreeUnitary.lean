module

public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6TTUnits
public import CFSG.LocalAnalysis.StandardType.GGTwE6KGA1Defs
import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6TTBridge
import CFSG.LocalAnalysis.StandardType.GGTwE6LemmaKFinal
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfE6Toral
import CFSG.LocalAnalysis.StandardType.GGLieM6cDescent
import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter

public section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.Open CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Lang.E6Descent CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.StandardType.TableBExc.E6Three (zetaVec)


theorem twE6LawPos_three_of_toral {f : ℕ} (hf : 1 ≤ f) (h3 : 3 ∣ 2 ^ f + 1)
    {E : Subgroup (ModGL (langTag .twistedE6) GGL)} (hER : E ≤ ggFixGp .twistedE6 f)
    (hE : IsElemAbelian 3 E) (hcard : 3 ^ 4 ≤ Nat.card E)
    (hXt : NoOffTwE6Three.IsToralE6 GGL E) : TwE6LawPos 3 f E := by
  obtain ⟨_, _⟩ := exists_algebra_isAlgClosure_ggl (GaloisField 2 (2 * f))
  obtain ⟨ζ, hζo⟩ := exists_zeta GGL Nat.prime_three (by norm_num)
  have hζ : ζ ^ 3 = 1 := by
    rw [← hζo]
    exact pow_orderOf_eq_one ζ
  obtain ⟨g, hg, hgn, hgx⟩ : ∃ g ∈ adjointGroup (langTag .twistedE6) GGL,
      g⁻¹ * ggPhi .twistedE6 f g = canonicalRep (coxeterSystem (langTag .twistedE6)) GGL twE6W0 ∧
      ∀ x ∈ E, ∃ v, x = g * rootDiagUnit (langTag .twistedE6) (zetaVec ζ hζ v) * g⁻¹ :=
    TwE6LemmaK.exists_lang_typeMinusOne_of_toral hf h3 GGL (ggFrobT f) (ggFrobT_apply f) hζ hζo
      hER hE hcard hXt
  refine twE6LawPos_of_lang le_rfl h3 hER hg hgn fun x hx => ?_
  obtain ⟨v, rfl⟩ := hgx x hx
  rw [show g⁻¹ * (g * rootDiagUnit (langTag .twistedE6) (zetaVec ζ hζ v) * g⁻¹) * g =
    rootDiagUnit (langTag .twistedE6) (zetaVec ζ hζ v) by group]
  exact rootDiagUnit_mem_torusGroup _

theorem twE6TTThreeUnitary : TwE6TTThreeUnitary := by
  intro f hf h9 E hER hE hcard
  have hXt : NoOffTwE6Three.IsToralE6 GGL E :=
    ExcFramesHalf.bigElemAbelianToralBar_E6_three (ZMod 2) (by rw [Nat.card_zmod]; norm_num) E
      (fun x hx => (Subgroup.mem_inf.1 (hER hx)).1)
      (fun x hx y hy => congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)) hE.2
      ((show (3 : ℕ) ^ (Tag.E6.rank - 1) = 3 ^ 5 from rfl).trans hcard.symm).le
  exact twE6LawPos_three_of_toral hf ((by norm_num : (3 : ℕ) ∣ 9).trans h9) hER hE
    ((by norm_num : (3 : ℕ) ^ 4 ≤ 3 ^ 5).trans hcard.ge) hXt

end CFSG.StandardType.LieKnownR2.ExcPos
