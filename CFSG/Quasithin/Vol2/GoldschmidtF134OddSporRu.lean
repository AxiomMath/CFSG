module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddSporArith
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu
import all CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatRu
public import CFSG.Sporadic.Ru
public import Certificates.Certificate3172
public import Certificates.Certificate4034
public import Certificates.Certificate4080
public import Certificates.Certificate4143
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Milestones.CL_LIT_SQTK_simple_list
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Inputs
public import CFSG.Sporadic.J4Base
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43
public import Certificates.Certificate8026Base

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Blueprint CFSG.QuasithinUnique.Ch1.SporLat

theorem noPowerOvergroup_ru :
    NoPowerOvergroup fun (X : Type) [Group X] =>
      Nonempty (X ≃* NativeSporadic.Carrier .Ru) := by
  refine noPowerOvergroup_of_overgroups (fun X _ _ ⟨e⟩ => ?_)
    (fun X _ _ ⟨e⟩ T Y hT hTY => ?_)
  · rw [Nat.card_congr e.toEquiv]
    show 3 ∣ Nat.card NativeSporadic.Ru
    rw [CFSG.Sporadic.Ru.card_Ru]
    norm_num
  · rcases Ru.ru_overgroups ⟨e⟩ hT hTY with h | ⟨m, hm, hcard, -, -⟩
    · exact Or.inl h
    · right
      have hrows : ∀ m ∈ Ru.ruMems, m.order = 2 ^ 14 ∨ 3 ∣ m.order := by decide +kernel
      rcases hrows m hm with h | h
      · exact Or.inl ⟨14, hcard.trans h⟩
      · exact Or.inr (hcard ▸ h)

end CFSG.Quasithin.H13.NQCore
