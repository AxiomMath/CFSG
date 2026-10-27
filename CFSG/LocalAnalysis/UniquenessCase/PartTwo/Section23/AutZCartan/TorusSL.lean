module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.AutZCartan.LineTorus
public import CFSG.Open.StatedDefs
import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194OmegaTorus
import CFSG.Open.StatedAPI
public import CFSG.Assembly.QuasithinDefs
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.Module
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.AutZC

open CFSG.Open Matrix
open CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven

variable {K : Type} [Field K]

theorem lineTorus_statedSL {d : ℕ} [NeZero d] (hd : 2 ≤ d) :
    LineTorus (StatedSL d K) (Pi.single 0 1) := by
  intro c
  have h01 : (0 : Fin d) ≠ 1 := by
    intro h
    have hv : (0 : ℕ) = 1 := by
      simpa [Fin.ext_iff, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < d)] using h
    exact Nat.zero_ne_one hv
  let t : Fin d → Kˣ := Pi.mulSingle 0 c * Pi.mulSingle 1 c⁻¹
  have hprod : (∏ i, t i) = 1 := by
    dsimp only [t]
    simp only [Pi.mul_apply]
    rw [Finset.prod_mul_distrib]
    simp [Finset.prod_pi_mulSingle']
  refine ⟨diagGL t, CFSG.Open.StatedAPI.mem_statedSL_of_det ?_, ?_⟩
  · rw [coe_diagGL, Matrix.det_diagonal]
    simpa [Units.coe_prod] using congrArg Units.val hprod
  · rw [mulVec_diagGL]
    funext i
    by_cases hi : i = 0
    · subst hi
      simp [t, Pi.mulSingle, h01]
    · simp [t, Pi.single_eq_of_ne hi]

end CFSG.LocalAnalysis.UniquenessCase.UC22.AutZC
