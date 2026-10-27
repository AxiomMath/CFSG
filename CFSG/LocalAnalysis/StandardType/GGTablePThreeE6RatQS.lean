module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabel
import CFSG.HardMathSupport.Timmesfeld.LangTorus.LangComponentsAll
import CFSG.HardMathSupport.Timmesfeld.LangTorus.CentralizerTrivialOuterThree
import CFSG.ClassicalInvolution.ModelFacts.PairFrameExcE8Rank1
import CFSG.ClassicalInvolution.ModelFacts.StandardPairDichotomyExcA2Generic
import CFSG.HardMathSupport.Timmesfeld.LangTorus.OuterField
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidField
import CFSG.HardMathSupport.Timmesfeld.LangTorus.RigidNorm
import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
import CFSG.RankThree.Classical2.TwistedE6Phi3A2Case
import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
import CFSG.RankThree.PartOne.KE.E7FiveBlock
import CFSG.RankThree.PartOne.KE.E8D4Family
import CFSG.RankThree.PartOne.KLCE.Sector

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Certificates

theorem e6_rationalComponent_quasisimple
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (S : LangSetup Tag.E6 L 3)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hap : ∀ j, a j ^ 3 = 1) (h1 : rootDiagUnit Tag.E6 a ≠ 1) (i : KernelComponent (rootCharHom a)) :
    CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  have hbig : ¬ Nat.Coprime 3 (Nat.card (rationalComponent S.ρ S.Γ (rootCharHom a) i)) :=
    threeBigComponents_holds Tag.E6 L S a hT h1 i
  have hpow : rootDiagUnit Tag.E6 a ^ 3 = 1 := by
    have ha3 : a ^ 3 = 1 := funext hap
    have hmap : rootDiagUnit Tag.E6 (a ^ 3) = rootDiagUnit Tag.E6 a ^ 3 :=
      map_pow (rootDiagUnitHom Tag.E6 L) a 3
    rw [← hmap, ha3, rootDiagUnit_one]
  exact langComponentsQuasisimpleT_all (twistKind S.ρ (rootCharHom a) i)
    Tag.E6 L 3 S a hT hpow h1 i rfl hbig

end Certificates

end CFSG.StandardType.TablePThreeKG

end
