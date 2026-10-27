module

public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6PairDictHolds
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6RootTransportHolds
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6FrameHolds
public import CFSG.LocalAnalysis.StandardType.ExcPos.TwE6PairTwo
public import Certificates.Certificate1952
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import Certificates.Certificate13659
public import Certificates.Certificate13660
import CFSG.GroupTheory.OddKernelImage
import CFSG.LocalAnalysis.StandardType.ExcPos.U1aPairInner
import CFSG.LocalAnalysis.StandardType.ExcPos.U1aPairOuter

public noncomputable section

namespace CFSG.StandardType.LieKnownR2.ExcPos

open CFSG.Assembly CFSG.Open CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.StandardType.LieCore CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.LieType.Universal CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem excRLeJ_holds : ExcRLeJStmt := by
  intro G H _ _ _ η hcen hodd R J hR h
  exact CFSG.GroupTheory.le_of_map_le_map_of_odd hcen hodd hR h

theorem twE6StablePair_holds :
    TwE6StablePairStmt := by
  intro f hf Δ hq ρ hρ hfin p hp hp2 a₁ a₂ ha₁ ha₂ hap₁ hap₂ hne iJ hb hqs
  have hτ : Tag.E6 = .E6 ∨ Tag.E6 = .E7 ∨ Tag.E6 = .E8 := Or.inl rfl
  by_cases hinner : twistInner (componentRoots (LieCore.jointChar a₁ a₂) iJ) ρ
  · exact exists_stable_pair_inner hτ hf Δ hq hρ hfin ha₁ ha₂ iJ hb hinner hqs
  · exact exists_stable_pair_outer hτ hf Δ hq hρ hfin hp hp2 ha₁ ha₂ hap₁ hap₂ hne iJ hb hinner hqs

theorem twE6PairOne_holds :
    TwE6PairOne :=
  twE6PairOne_of_pieces twE6PairDict_holds twE6StablePair_holds twE6RootTransport_holds
    excRLeJ_holds

theorem excU1b_holds :
    ExcU1b :=
  excU1b_of_frame_pair twE6Frame_holds (twE6PairSel_of_one_two twE6PairOne_holds twE6PairTwo_holds)

end CFSG.StandardType.LieKnownR2.ExcPos
