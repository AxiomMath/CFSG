module

public import CFSG.RankThree.PartOne.KP.MSection
public import CFSG.Monster.SteinbergMY443NativeSurjective
public import CFSG.Monster.Existence.DLevelRank
public import CFSG.Sporadic.Bridge.Y443Relabel
public import CFSG.Sporadic.Bridge.MonsterModels
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3027
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate6001
public import Certificates.Certificate6002
public import Certificates.Certificate6003
public import Certificates.Certificate6004
public import Certificates.Certificate6005
public import Certificates.Certificate6006
public import Certificates.Certificate6009
public import Certificates.Certificate6010
public import Certificates.Certificate6011
public import Certificates.Certificate6012
public import Certificates.Certificate6013
public import Certificates.Certificate6014
public import Certificates.Certificate6015
public import Certificates.Certificate6016
public import Certificates.Certificate6017
public import Certificates.Certificate6018
public import Certificates.Certificate9201
public import Certificates.Certificate10027
public import Certificates.Certificate10093
public import Certificates.Certificate10095
public import Certificates.Certificate10098
public import Certificates.Certificate10100
public import Certificates.Certificate10101
public import Certificates.Certificate10102
public import Certificates.Certificate10103
public import Certificates.Certificate10104
public import Certificates.Certificate10107
public import Certificates.Certificate10108
public import Certificates.Certificate10110
public import Certificates.Certificate10111
public import Certificates.Certificate10127
public import Certificates.Certificate16018
public import Certificates.Certificate16026
public import Certificates.Certificate6007
public import Certificates.Certificate10115
public import Certificates.Certificate10116
public import Certificates.Certificate10117
public import Certificates.Certificate10118
public import Certificates.Certificate10119
public import Certificates.Certificate10123
public import CFSG.Assembly.QuasithinDefs
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.Basic
public import CFSG.RankThree.PartOne.KP.MReduction
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Basic
public import CFSG.YGroups.DCE.MaximalB
public import CFSG.YGroups.Y443.Native.AlignB
public import CFSG.YGroups.Y443.Native.AlignW
public import CFSG.YGroups.Y443.Native.CosetData
public import CFSG.YGroups.Y443.Native.Image

public section

namespace CFSG.RankThree.PartOne

open CFSG.Open CFSG.Monster.Generated CFSG.Monster.B CFSG.Monster.Existence CFSG.YGroups.Y443

theorem simplePresentationMHasBSection_holds : SimplePresentationMHasBSection := by
  intro T _ _ _ _ ⟨e⟩
  have eM : T ≃* MonsterY443Derived :=
    e.trans CFSG.Blueprint.NativeSporadic.MonsterModel.y443DerivedEquivOpen
  have hsimple : IsSimpleGroup MonsterY443Derived := MulEquiv.isSimpleGroup eM.symm
  have hinj : Function.Injective fM := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (fM.ker) with h | h
    · exact h
    · exact absurd h fM_ker_ne_top
  have hsurj : Function.Surjective fM :=
    ((y443_native_surjective_homomorphism).1 fM fM_isFM).1
  exact exists_section_of_equiv_of_le Gmat (eM.trans (MulEquiv.ofBijective fM ⟨hinj, hsurj⟩))
    Cgen Cgen_le_Gmat Zstar phiB

end CFSG.RankThree.PartOne
