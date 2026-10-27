module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporSchreier
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J4OutFinal
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113DetList
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.C2Defs
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace C41Pf

theorem schreierFactListCat_proved
    : Vol2Native.SchreierFactListCat := by
  have : Finite (CFSG.Blueprint.NativeSporadic.Carrier .J4) :=
    CFSG.Sporadic.J4.fam_j4_simplicity.1
  have : Finite (MulAut (CFSG.Blueprint.NativeSporadic.Carrier .J4)) :=
    Finite.of_injective (fun α : MulAut (CFSG.Blueprint.NativeSporadic.Carrier .J4) =>
      (α : CFSG.Blueprint.NativeSporadic.Carrier .J4 → CFSG.Blueprint.NativeSporadic.Carrier .J4))
      DFunLike.coe_injective
  have : Finite (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (CFSG.Blueprint.NativeSporadic.Carrier .J4)) :=
    Finite.of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  have hJ4 : CFSG.QuasithinUnique.Ch1.J4OutOdd := Setup.X1.j4OuterOdd
  exact Vol2Native.schreierFactListCat_of_J4
    (CFSG.ComponentClassification.SporadicSchreierDispatch.sporadicSchreierCase_of_outer
      (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hJ4))

variable {G : Type} [Group G] [Finite G]

theorem outSolvable_of_isSQTKIn
    (K : Subgroup G) (hK : IsSQTKIn K) (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) :
    OutSolvable (↥K ⧸ CFSG.pCore 2 ↥K) := by
  have hSQ : Bridge.IsSQTKQuotient CFSG.SectionRank.IsKGroupCat (↥K ⧸ CFSG.pCore 2 ↥K) :=
    ⟨↥K, inferInstance, inferInstance, QuotientGroup.mk' _, QuotientGroup.mk'_surjective _,
      hK.1, hK.2⟩
  have hlist := Bridge.B113Det.sqtkSimpleList_of_quasisimple (MonoidHom.id _)
    Function.injective_id hSQ hq
  exact schreierFactListCat_proved _ hq hlist

end C41Pf

end CFSG.Quasithin
