module

import CFSG.Sporadic.Bridge.M11
import CFSG.Sporadic.Bridge.M12
import CFSG.Sporadic.Bridge.M22
import CFSG.Sporadic.Bridge.M23Surj
import CFSG.Sporadic.Bridge.M24Surj
import CFSG.Sporadic.Bridge.J1
import CFSG.Sporadic.Bridge.J2
import CFSG.Sporadic.Bridge.J3Surj
import CFSG.Sporadic.Bridge.HSSurj
import CFSG.Sporadic.Bridge.Co3Surj
import CFSG.Sporadic.Bridge.ONSurj
import CFSG.Sporadic.Bridge.HNSurj
import CFSG.Sporadic.Bridge.ThSurj
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Seed.McL
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Seed.He
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Seed.Ru
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Seed.Co2
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Seed.Suz
import CFSG.RankThree.PartTwo.Census.Sporadic.J4Bridge
import CFSG.RankThree.PartTwo.Census.Sporadic.LyBridge
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.RankThree.PartOne.Census3.Interface

public section

namespace CFSG.RankThree.PartOne.Census3

open TauCeti CFSG.Blueprint

abbrev ThmThreeItem6Native (G : Type) [Group G] : Prop :=
  ∃ s ∈ sporadicsThm3, Nonempty (G ≃* NativeSporadic.Carrier s)

@[expose] def TheoremThreeListNative (G : Type) [Group G] : Prop :=
  ThmThreeItem1 G ∨ ThmThreeItem2 G ∨ ThmThreeItem3 G ∨ ThmThreeItem4 G ∨ ThmThreeItem5 G ∨
    ThmThreeItem6Native G ∨ ThmThreeItem7 G ∨ ThmThreeItem8 G ∨ ThmThreeItem9 G

theorem nonempty_carrier_mulEquiv_of_mem {s : SporadicName} (hs : s ∈ sporadicsThm3)
    [IsSimpleGroup s.Group] : Nonempty (NativeSporadic.Carrier s ≃* s.Group) := by
  cases s
  case M11 => exact CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  case M12 => exact CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
  case M22 => exact CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  case M23 => exact CFSG.Sporadic.Bridge.M23.nonempty_mulEquiv
  case M24 => exact CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv
  case J1 => exact CFSG.Sporadic.Bridge.J1.nonempty_mulEquiv
  case J2 => exact CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv
  case J3 => exact CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  case J4 => exact CFSG.RankThree.PartTwo.Census.nonempty_mulEquiv_carrier_J4.map MulEquiv.symm
  case McL => exact CFSG.QuasithinUnique.SQTK.nonempty_mulEquiv_carrier_McL.map MulEquiv.symm
  case Ly => exact CFSG.RankThree.PartTwo.Census.nonempty_mulEquiv_Ly.map MulEquiv.symm
  case HS => exact CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  case He => exact CFSG.QuasithinUnique.SQTK.nonempty_mulEquiv_carrier_He.map MulEquiv.symm
  case Suz => exact CFSG.QuasithinUnique.SQTK.nonempty_mulEquiv_carrier_Suz.map MulEquiv.symm
  case Ru => exact CFSG.QuasithinUnique.SQTK.nonempty_mulEquiv_carrier_Ru.map MulEquiv.symm
  case ONan => exact CFSG.Sporadic.Bridge.ON.nonempty_mulEquiv
  case Co3 => exact CFSG.Sporadic.Bridge.Co3.nonempty_mulEquiv
  case Co2 => exact CFSG.QuasithinUnique.SQTK.nonempty_mulEquiv_carrier_Co2.map MulEquiv.symm
  case HN => exact CFSG.Sporadic.Bridge.HN.nonempty_mulEquiv
  case Th => exact CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv
  all_goals simp [sporadicsThm3] at hs

theorem TheoremThreeList.native {G : Type} [Group G] [IsSimpleGroup G] (h : TheoremThreeList G) :
    TheoremThreeListNative G := by
  rcases h with h | h | h | h | h | ⟨s, hs, ⟨e⟩⟩ | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · have : IsSimpleGroup s.Group := e.symm.isSimpleGroup
    obtain ⟨b⟩ := nonempty_carrier_mulEquiv_of_mem hs
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨s, hs, ⟨e.trans b.symm⟩⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))

end CFSG.RankThree.PartOne.Census3
